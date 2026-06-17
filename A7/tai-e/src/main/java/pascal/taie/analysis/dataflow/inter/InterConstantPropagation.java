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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    record _InstanceField(Var base, JField field) {
    }

    record _ArrayIndex(Var base, Value index) {
    }

    /**
     * 表示一个可能具有别名的值对象。
     * 例如：a 和 b 互为别名，则 a.f 和 b.f 是同一个 ReferenceValue 实例。当 a.f 的 value 改变时，所有别名也跟着改变，且在调用处将 loadStmts 加入 worklist。
     */
    class ReferenceValue {
        public Value value;
        public Set<Stmt> loadStmts;

        public ReferenceValue() {
            value = Value.getUndef();
            loadStmts = new HashSet<>();
        }

        public boolean meetValue(Value target) {
            var oldValue = value;
            value = cp.meetValue(value, target);
            return value != oldValue;
        }
    }

    private Map<Var, Set<Var>> aliases;

    private final Map<JField, ReferenceValue> staticFieldValues = new HashMap<>();

    private final Map<_InstanceField, ReferenceValue> instanceFieldValues = new HashMap<>();

    private final Map<_ArrayIndex, ReferenceValue> indexValues = new HashMap<>();

    private Map<Var, Set<Var>> findAliases(PointerAnalysisResult pta) {
        var result = new HashMap<Var, Set<Var>>();
        for (var v1 : pta.getVars()) {
            var pts1 = pta.getPointsToSet(v1);
            for (var v2 : pta.getVars()) {
                if (v1.equals(v2))
                    continue;
                var pts2 = pta.getPointsToSet(v2);
                if (pts1.stream().anyMatch(pts2::contains)) {
                    // 确定了 v1 和 v2 是别名
                    result.putIfAbsent(v1, new HashSet<>());
                    result.putIfAbsent(v2, new HashSet<>());
                    result.get(v1).add(v2);
                    result.get(v2).add(v1);
                }
            }
        }
        return result;
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        aliases = findAliases(pta);
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        var old_out = out.copy();
        out.clear();
        out.copyFrom(in);

        if (stmt instanceof FieldStmt<?, ?> fieldStmt) {
            FieldAccess fieldAccess = fieldStmt.getFieldAccess();
            JField field = fieldStmt.getFieldRef().resolve();

            ReferenceValue ref = null;
            if (fieldAccess instanceof StaticFieldAccess) {
                if (!staticFieldValues.containsKey(field)) {
                    staticFieldValues.put(field, new ReferenceValue());
                }
                ref = staticFieldValues.get(field);
            } else if (fieldAccess instanceof InstanceFieldAccess ifa) {
                Var v = ifa.getBase();
                var key = new _InstanceField(v, field);
                if (!instanceFieldValues.containsKey(key) && aliases.containsKey(v)) {
                    for (var alias : aliases.get(v)) {
                        var aliasKey = new _InstanceField(alias, field);
                        if (instanceFieldValues.containsKey(aliasKey)) {
                            instanceFieldValues.put(key, instanceFieldValues.get(aliasKey));
                            break;
                        }
                    }
                }
                instanceFieldValues.putIfAbsent(key, new ReferenceValue());
                ref = instanceFieldValues.get(key);
            }

            if (ref != null) {
                if (fieldStmt instanceof StoreField storeStmt) {
                    Value rhs = ConstantPropagation.evaluate(storeStmt.getRValue(), in);
                    if (ref.meetValue(rhs)) {
                        solver.workListAddAll(ref.loadStmts);
                    }
                } else if (fieldStmt instanceof LoadField loadStmt) {
                    ref.loadStmts.add(loadStmt);
                    var lvar = loadStmt.getLValue();
                    if (ConstantPropagation.canHoldInt(lvar)) {
                        out.update(lvar, ref.value);
                    }
                }
            }
        } else if (stmt instanceof StoreArray sa) {
            // TODO
        } else if (stmt instanceof LoadArray la) {
            // TODO
        } else if (stmt instanceof DefinitionStmt<?, ?> def
                && def.getLValue() instanceof Var lvar
                && ConstantPropagation.canHoldInt(lvar)) {
            out.update(lvar, ConstantPropagation.evaluate(def.getRValue(), in));
        }

        return !out.equals(old_out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        var in = out.copy();
        var stmt = edge.getSource();
        stmt.getDef().ifPresent(lVal -> {
            if (lVal instanceof Var v)
                in.remove(v);
        });
        return in;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        var invoke_exp = (InvokeExp) edge.getSource().getUses().stream()
                .filter(e -> e instanceof InvokeExp).findFirst().orElse(null);
        if (invoke_exp == null)
            return new CPFact();
        var actual = invoke_exp.getArgs().iterator();
        var formal = edge.getCallee().getIR().getParams().iterator();
        var in = new CPFact();
        while (actual.hasNext() && formal.hasNext()) {
            in.update(formal.next(), callSiteOut.get(actual.next()));
        }
        return in;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        var formal = edge.getCallSite().getDef().orElse(null);
        if (!(formal instanceof Var))
            return new CPFact();

        Value ret_value = Value.getUndef();
        for (var name : edge.getReturnVars()) {
            ret_value = cp.meetValue(ret_value, returnOut.get(name));
        }
        var in = new CPFact();
        in.update((Var) formal, ret_value);
        return in;
    }
}
