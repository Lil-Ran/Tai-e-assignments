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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.HashSet;
import java.util.LinkedList;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        boolean hasChanged = true;
        while (hasChanged) {
            hasChanged = false;
            var unvisited = new HashSet<>(cfg.getNodes());
            var queue = new LinkedList<Node>();
            Node exit = cfg.getExit();
            queue.add(exit);
            while (!queue.isEmpty()) {
                var front = queue.remove();
                for (var pred : cfg.getPredsOf(front)) {
                    if (!unvisited.contains(pred))
                        continue;
                    unvisited.remove(pred);
                    queue.add(pred);
                    ((SetFact<?>)result.getOutFact(pred)).clear();
                    for (var succ : cfg.getSuccsOf(pred)) {
                        analysis.meetInto(result.getInFact(succ), result.getOutFact(pred));
                    }
                    hasChanged = hasChanged || analysis.transferNode(
                            pred, result.getInFact(pred), result.getOutFact(pred)
                    );
                }
            }
        }
    }
}
