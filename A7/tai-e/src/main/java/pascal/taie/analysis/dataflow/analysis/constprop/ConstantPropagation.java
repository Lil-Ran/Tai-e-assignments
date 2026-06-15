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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        var fact = new CPFact();
        for (var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((k, v) -> target.update(k, meetValue(v, target.get(k))));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;
        if (v1.getConstant() != v2.getConstant()) return Value.getNAC();
        return v1;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        var old_out = out.copy();
        out.clear();
        out.copyFrom(in);
        if (stmt instanceof DefinitionStmt<?, ?> def_stmt
                && def_stmt.getLValue() instanceof Var lvar
                && canHoldInt(lvar)) {
            out.update(lvar, evaluate(def_stmt.getRValue(), in));
        }
        return !out.equals(old_out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        if (exp instanceof Var) {
            return in.get((Var) exp);
        }
        if (!(exp instanceof BinaryExp)) {
            return Value.getNAC();
        }
        Value operand1 = in.get(((BinaryExp) exp).getOperand1());
        Value operand2 = in.get(((BinaryExp) exp).getOperand2());
        // NAC / 0 => UNDEF
        if (operand2.isConstant()
                && operand2.getConstant() == 0
                && exp instanceof ArithmeticExp exp1
                && (exp1.getOperator() == ArithmeticExp.Op.DIV
                || exp1.getOperator() == ArithmeticExp.Op.REM)) {
            return Value.getUndef();
        }
        if (operand1.isNAC() || operand2.isNAC()) {
            return Value.getNAC();
        }
        if (operand1.isUndef() || operand2.isUndef()) {
            return Value.getUndef();
        }
        int const1 = operand1.getConstant();
        int const2 = operand2.getConstant();
        if (exp instanceof ArithmeticExp exp1) {
            return switch (exp1.getOperator()) {
                case ADD -> Value.makeConstant(const1 + const2);
                case SUB -> Value.makeConstant(const1 - const2);
                case MUL -> Value.makeConstant(const1 * const2);
                case DIV -> const2 == 0 ? Value.getUndef() : Value.makeConstant(const1 / const2);
                case REM -> const2 == 0 ? Value.getUndef() : Value.makeConstant(const1 % const2);
            };
        }
        if (exp instanceof BitwiseExp exp1) {
            return switch (exp1.getOperator()) {
                case AND -> Value.makeConstant(const1 & const2);
                case OR -> Value.makeConstant(const1 | const2);
                case XOR -> Value.makeConstant(const1 ^ const2);
            };
        }
        if (exp instanceof ShiftExp exp1) {
            return switch (exp1.getOperator()) {
                case SHL -> Value.makeConstant(const1 << const2);
                case SHR -> Value.makeConstant(const1 >> const2);
                case USHR -> Value.makeConstant(const1 >>> const2);
            };
        }
        if (exp instanceof ConditionExp exp1) {
            return switch (exp1.getOperator()) {
                case EQ -> Value.makeConstant(const1 == const2 ? 1 : 0);
                case NE -> Value.makeConstant(const1 != const2 ? 1 : 0);
                case LT -> Value.makeConstant(const1 < const2 ? 1 : 0);
                case GT -> Value.makeConstant(const1 > const2 ? 1 : 0);
                case LE -> Value.makeConstant(const1 <= const2 ? 1 : 0);
                case GE -> Value.makeConstant(const1 >= const2 ? 1 : 0);
            };
        }
        return Value.getNAC();
    }
}
