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
        if (callGraph.contains(method))
            return;
        callGraph.addReachableMethod(method);
        for (var stmt : method.getIR().getStmts()) {
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
            workList.addEntry(varPtr, new PointsToSet(obj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            var l = pointerFlowGraph.getVarPtr(stmt.getLValue());
            var r = pointerFlowGraph.getVarPtr(stmt.getRValue());
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
            addPFGEdge(fp, lhs);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
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
            var difference = propagate(p, pts);
            if (!(p instanceof VarPtr vp))
                continue;
            var v = vp.getVar();
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
            var pThis = method.getIR().getThis();
            if (pThis != null) {
                workList.addEntry(pointerFlowGraph.getVarPtr(pThis), new PointsToSet(recv));
            }
            processAnyCallSite(invoke, method);
        }
    }

    private void processAnyCallSite(Invoke invoke, JMethod method) {
        if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method))) {
            addReachable(method);
            var actual = invoke.getInvokeExp().getArgs().iterator();
            var formal = method.getIR().getParams().iterator();
            while (actual.hasNext() && formal.hasNext()) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(actual.next()),
                        pointerFlowGraph.getVarPtr(formal.next())
                );
            }
            if (invoke.getResult() != null) {
                for (var ret : method.getIR().getReturnVars()) {
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(ret),
                            pointerFlowGraph.getVarPtr(invoke.getResult())
                    );
                }
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
