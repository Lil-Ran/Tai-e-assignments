/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // 对 new/赋值/静态调用/静态字段访问 只需要每个方法处理一次
        // 副产物：构建调用图
        if (!callGraph.addReachableMethod(csMethod))
            return;
        // 将上下文打包进 StmtProcessor
        var stmtProcessor = new StmtProcessor(csMethod);
        for (var stmt : csMethod.getMethod().getIR().getStmts()) {
            // 用访问者模式处理关注的每条语句，添加 PFG 边
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            var varPtr = csManager.getCSVar(context, stmt.getLValue());
            // 堆敏感：仅与 new 语句相关
            var heapObj = heapModel.getObj(stmt);
            var heapContext = contextSelector.selectHeapContext(csMethod, heapObj);
            var csObj = csManager.getCSObj(heapContext, heapObj);
            // new 语句直接将对象加入变量的 points-to set 中
            workList.addEntry(varPtr, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            var l = csManager.getCSVar(context, stmt.getLValue());
            var r = csManager.getCSVar(context, stmt.getRValue());
            // 赋值语句在 PFG 中添加边
            addPFGEdge(r, l);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic())
                return null;
            var method = resolveCallee(null, stmt);
            if (method == null)
                return null;
            var csCallSite = csManager.getCSCallSite(context, stmt);
            var calleeContext = contextSelector.selectContext(csCallSite, method);
            var csCallee = csManager.getCSMethod(calleeContext, method);
            // 处理静态调用语句（传参、返回值），与实例调用语句共用逻辑
            processAnyCallSite(csCallSite, csCallee);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (!stmt.isStatic())
                return null;
            var field = stmt.getFieldRef().resolve();
            var fp = csManager.getStaticField(field);
            var rhs = csManager.getCSVar(context, stmt.getRValue());
            // 静态字段赋值语句在 PFG 中添加边
            addPFGEdge(rhs, fp);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (!stmt.isStatic())
                return null;
            var field = stmt.getFieldRef().resolve();
            var fp = csManager.getStaticField(field);
            var lhs = csManager.getCSVar(context, stmt.getLValue());
            // 静态字段读取语句在 PFG 中添加边
            addPFGEdge(fp, lhs);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // 如果边已存在则直接返回
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                // 准备将 source 的 points-to set 传播到 target
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var p = entry.pointer();
            var pts = entry.pointsToSet();
            // 如果有新的目标被加入 p 的 points-to set 中，则将这些目标传播到 p 的 PFG 后继
            var difference = propagate(p, pts);
            if (!(p instanceof CSVar vp))
                continue;
            var varPtr = vp.getVar();
            var varContext = vp.getContext();
            // 对于新发现的每个目标，一并处理对应变量相关的实例字段访问和实例调用语句，发现新的 PFG 边
            for (var obj : difference) {
                for (var stmt : varPtr.getStoreFields()) {
                    var field = stmt.getFieldRef().resolve();
                    var fp = csManager.getInstanceField(obj, field);
                    var rhs = csManager.getCSVar(varContext, stmt.getRValue());
                    addPFGEdge(rhs, fp);
                }
                for (var stmt : varPtr.getLoadFields()) {
                    var field = stmt.getFieldRef().resolve();
                    var fp = csManager.getInstanceField(obj, field);
                    var lhs = csManager.getCSVar(varContext, stmt.getLValue());
                    addPFGEdge(fp, lhs);
                }
                for (var stmt : varPtr.getStoreArrays()) {
                    var arr = csManager.getArrayIndex(obj);
                    var rhs = csManager.getCSVar(varContext, stmt.getRValue());
                    addPFGEdge(rhs, arr);
                }
                for (var stmt : varPtr.getLoadArrays()) {
                    var arr = csManager.getArrayIndex(obj);
                    var lhs = csManager.getCSVar(varContext, stmt.getLValue());
                    addPFGEdge(arr, lhs);
                }
                processCall(vp, obj);
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var difference = PointsToSetFactory.make();
        // difference = pointsToSet - pointer.getPointsToSet()
        pointsToSet.objects()
                .filter(element -> !pointer.getPointsToSet().contains(element))
                .forEach(difference::addObject);
        if (!difference.isEmpty()) {
            // pointer.getPointsToSet() += difference
            for (var element : difference) {
                pointer.getPointsToSet().addObject(element);
            }
            for (var succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, difference);
            }
        }
        return difference;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // caller 的上下文是变量 recv 所属方法的上下文
        var callerContext = recv.getContext();
        for (var invoke : recv.getVar().getInvokes()) {
            var csCallSite = csManager.getCSCallSite(callerContext, invoke);
            var method = resolveCallee(recvObj, invoke);
            if (method == null)
                continue;
            // callee 的上下文由 callsite（caller 上下文）、接收对象和被调用方法共同决定
            var calleeContext = contextSelector.selectContext(csCallSite, recvObj, method);
            // 传递 this 指针
            var pThis = method.getIR().getThis();
            if (pThis != null) {
                workList.addEntry(csManager.getCSVar(calleeContext, pThis), PointsToSetFactory.make(recvObj));
            }
            var csMethod = csManager.getCSMethod(calleeContext, method);
            // 处理实例调用语句（传参、返回值），与静态调用语句共用逻辑
            processAnyCallSite(csCallSite, csMethod);
        }
    }

    private void processAnyCallSite(CSCallSite csCallSite, CSMethod csMethod) {
        var callerContext = csCallSite.getContext();
        var invoke = csCallSite.getCallSite();
        var calleeContext = csMethod.getContext();
        var method = csMethod.getMethod();
        // 对应对象的某些方法调用已经被处理过了，则不再处理
        if (!callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csMethod)))
            return;
        // 发现新的可达方法
        addReachable(csMethod);
        // 传递参数
        var actual = invoke.getInvokeExp().getArgs().iterator();
        var formal = method.getIR().getParams().iterator();
        while (actual.hasNext() && formal.hasNext()) {
            addPFGEdge(
                    csManager.getCSVar(callerContext, actual.next()),
                    csManager.getCSVar(calleeContext, formal.next())
            );
        }
        // 如果 caller 没有丢弃返回值，则传递返回值
        if (invoke.getResult() != null) {
            // 可能有多个 return 语句，传递所有对应变量
            for (var ret : method.getIR().getReturnVars()) {
                addPFGEdge(
                        csManager.getCSVar(calleeContext, ret),
                        csManager.getCSVar(callerContext, invoke.getResult())
                );
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
