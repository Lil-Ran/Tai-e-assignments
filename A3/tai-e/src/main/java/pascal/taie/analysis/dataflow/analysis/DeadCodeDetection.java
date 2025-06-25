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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        var visited = new HashSet<Stmt>();
        var worklist = new LinkedHashSet<Stmt>();
        worklist.add(cfg.getEntry());
        while (!worklist.isEmpty()) {
            var stmt = worklist.stream().findFirst().get();
            worklist.remove(stmt);

            // Yes we reached this stmt
            if (visited.contains(stmt))
                continue;
            visited.add(stmt);

            // Useless assignment:
            // is assignment; lVal is Var; lVal not alive; rVal has no side effect
            // Otherwise: handle at the end of this while loop
            if (stmt instanceof AssignStmt<?, ?> assign
                    && assign.getLValue() instanceof Var lVal
                    && !liveVars.getOutFact(stmt).contains(lVal)
                    && hasNoSideEffect(assign.getRValue())
            ) {
                // It's reachable but useless
                deadCode.add(stmt);
                worklist.addAll(cfg.getSuccsOf(stmt));
                continue;
            }

            if (stmt instanceof If if_stmt) {
                var cond_exp = if_stmt.getCondition();
                var operand1 = cond_exp.getOperand1();
                var operand2 = cond_exp.getOperand2();

                // Not all constants, every branch can be reached
                if (!constants.getInFact(stmt).get(operand1).isConstant()
                        || !constants.getInFact(stmt).get(operand2).isConstant()) {
                    worklist.addAll(cfg.getSuccsOf(stmt));
                    continue;
                }

                int const1 = constants.getInFact(stmt).get(operand1).getConstant();
                int const2 = constants.getInFact(stmt).get(operand2).getConstant();
                var op = cond_exp.getOperator();
                var compare_result = switch (op) {
                    case EQ -> const1 == const2;
                    case NE -> const1 != const2;
                    case LT -> const1 < const2;
                    case LE -> const1 <= const2;
                    case GT -> const1 > const2;
                    case GE -> const1 >= const2;
                };

                // Only one branch is known to be reached here
                var edges = cfg.getOutEdgesOf(stmt);
                var reachable = edges.stream().filter(e ->
                        e.getKind() == (compare_result ? Edge.Kind.IF_TRUE : Edge.Kind.IF_FALSE)
                ).findFirst();
                if (reachable.isPresent()) {
                    worklist.add(reachable.get().getTarget());
                    continue;
                }
            }

            // If not constant condition: handle at the end of this while loop
            if (stmt instanceof SwitchStmt switch_stmt
                    && constants.getInFact(stmt).get(switch_stmt.getVar()).isConstant()) {
                int constant = constants.getInFact(stmt).get(switch_stmt.getVar()).getConstant();
                // Only one branch is known to be reached here
                var edges = cfg.getOutEdgesOf(stmt);
                var reachable = edges.stream().filter(e ->
                        e.isSwitchCase() && e.getCaseValue() == constant
                ).findFirst();
                if (reachable.isPresent()) {
                    worklist.add(reachable.get().getTarget());
                } else {
                    worklist.add(switch_stmt.getDefaultTarget());
                }
                continue;
            }
            
            // Till now no sign that indicates unreachable, so they are reachable
            worklist.addAll(cfg.getSuccsOf(stmt));
        }

        deadCode.addAll(cfg.getNodes().stream().filter(
                stmt -> !visited.contains(stmt) && !cfg.isEntry(stmt) && !cfg.isExit(stmt)
        ).toList());
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
