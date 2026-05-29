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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // 对 new/赋值/静态调用/静态字段访问 只需要每个方法处理一次
        if (callGraph.contains(method))
            return;
        // 副产物：构建调用图
        callGraph.addReachableMethod(method);
        for (var stmt : method.getIR().getStmts()) {
            // 用访问者模式处理关注的每条语句，添加 PFG 边
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New stmt) {
            var varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            var obj = heapModel.getObj(stmt);
            // new 语句直接将对象加入变量的 points-to set 中
            workList.addEntry(varPtr, new PointsToSet(obj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            var l = pointerFlowGraph.getVarPtr(stmt.getLValue());
            var r = pointerFlowGraph.getVarPtr(stmt.getRValue());
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
            // 处理静态调用语句（传参、返回值），与实例调用语句共用逻辑
            processAnyCallSite(stmt, method);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (!stmt.isStatic())
                return null;
            var field = stmt.getFieldRef().resolve();
            var fp = pointerFlowGraph.getStaticField(field);
            var rhs = pointerFlowGraph.getVarPtr(stmt.getRValue());
            // 静态字段赋值语句在 PFG 中添加边
            addPFGEdge(rhs, fp);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (!stmt.isStatic())
                return null;
            var field = stmt.getFieldRef().resolve();
            var fp = pointerFlowGraph.getStaticField(field);
            var lhs = pointerFlowGraph.getVarPtr(stmt.getLValue());
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
            if (!(p instanceof VarPtr vp))
                continue;
            var v = vp.getVar();
            // 对于新发现的每个目标，一并处理对应变量相关的实例字段访问和实例调用语句，发现新的 PFG 边
            for (var obj : difference) {
                for (var stmt : v.getStoreFields()) {
                    var field = stmt.getFieldRef().resolve();
                    var fp = pointerFlowGraph.getInstanceField(obj, field);
                    var rhs = pointerFlowGraph.getVarPtr(stmt.getRValue());
                    addPFGEdge(rhs, fp);
                }
                for (var stmt : v.getLoadFields()) {
                    var field = stmt.getFieldRef().resolve();
                    var fp = pointerFlowGraph.getInstanceField(obj, field);
                    var lhs = pointerFlowGraph.getVarPtr(stmt.getLValue());
                    addPFGEdge(fp, lhs);
                }
                for (var stmt : v.getStoreArrays()) {
                    var arr = pointerFlowGraph.getArrayIndex(obj);
                    var rhs = pointerFlowGraph.getVarPtr(stmt.getRValue());
                    addPFGEdge(rhs, arr);
                }
                for (var stmt : v.getLoadArrays()) {
                    var arr = pointerFlowGraph.getArrayIndex(obj);
                    var lhs = pointerFlowGraph.getVarPtr(stmt.getLValue());
                    addPFGEdge(arr, lhs);
                }
                processCall(v, obj);
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var difference = new PointsToSet();
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
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (var invoke : var.getInvokes()) {
            var method = resolveCallee(recv, invoke);
            if (method == null)
                continue;
            // 传递 this 指针
            var pThis = method.getIR().getThis();
            if (pThis != null) {
                workList.addEntry(pointerFlowGraph.getVarPtr(pThis), new PointsToSet(recv));
            }
            // 处理实例调用语句（传参、返回值），与静态调用语句共用逻辑
            processAnyCallSite(invoke, method);
        }
    }

    private void processAnyCallSite(Invoke invoke, JMethod method) {
        // 对应对象的某些方法调用已经被处理过了，则不再处理
        if (!callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method)))
            return;
        // 发现新的可达方法
        addReachable(method);
        // 传递参数
        var actual = invoke.getInvokeExp().getArgs().iterator();
        var formal = method.getIR().getParams().iterator();
        while (actual.hasNext() && formal.hasNext()) {
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(actual.next()),
                    pointerFlowGraph.getVarPtr(formal.next())
            );
        }
        // 如果 caller 没有丢弃返回值，则传递返回值
        if (invoke.getResult() != null) {
            // 可能有多个 return 语句，传递所有对应变量
            for (var ret : method.getIR().getReturnVars()) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(ret),
                        pointerFlowGraph.getVarPtr(invoke.getResult())
                );
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
