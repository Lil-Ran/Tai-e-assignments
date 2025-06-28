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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        var worklist = new ArrayDeque<JMethod>();
        worklist.push(entry);
        while (!worklist.isEmpty()) {
            var method = worklist.pop();
            if (callGraph.contains(method))
                continue;
            callGraph.addReachableMethod(method);
            for (var callSite : callGraph.callSitesIn.get(method)) {
                for (var m : resolve(callSite)) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, m));
                    worklist.push(m);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        var result = new HashSet<JMethod>();
        var method = callSite.getMethodRef();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC -> {
                result.add(method.getDeclaringClass().getDeclaredMethod(method.getSubsignature()));
            }
            case SPECIAL -> {
                var targetMethod = dispatch(method.getDeclaringClass(), method.getSubsignature());
                if (targetMethod != null) {
                    result.add(targetMethod);
                }
            }
            case VIRTUAL, INTERFACE -> {
                var subclasses = new HashSet<JClass>();
                subclasses.add(method.getDeclaringClass());
                while (!subclasses.isEmpty()) {
                    var jclass = subclasses.stream().findFirst().get();
                    subclasses.remove(jclass);
                    var targetMethod = dispatch(jclass, method.getSubsignature());
                    if (targetMethod != null) {
                        result.add(targetMethod);
                    }
                    if (jclass.isInterface()) {
                        subclasses.addAll(hierarchy.getDirectSubinterfacesOf(jclass));
                        subclasses.addAll(hierarchy.getDirectImplementorsOf(jclass));
                    } else {
                        subclasses.addAll(hierarchy.getDirectSubclassesOf(jclass));
                    }
                }
            }
        }
        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass == null)
            return null;
        var candidate = jclass.getDeclaredMethod(subsignature);
        if (candidate != null && !candidate.isAbstract())
            return candidate;
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
