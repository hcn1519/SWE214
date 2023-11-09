package analysis.exercise2;


import analysis.CallGraph;
import analysis.Helper;
import analysis.exercise1.CHAAlgorithm;
import soot.*;

import java.util.*;
import java.util.stream.Collectors;

public class RTAAlgorithm extends CHAAlgorithm  {

    @Override
    protected String getAlgorithm() {
        return "RTA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph cg) {
        soot.Hierarchy hierarchy = scene.getActiveHierarchy();
        for (SootMethod rootMethod : this.getEntryPoints(scene).collect(Collectors.toList())) {
            Queue<SootMethod> queue = new ArrayDeque<>();
            queue.add(rootMethod);
            cg.addNode(rootMethod);

            while (!queue.isEmpty()) {
                SootMethod srcMethod = queue.poll();
                if (!srcMethod.hasActiveBody())
                    continue;

                Body body = srcMethod.getActiveBody();
                for (Unit unit : body.getUnits()) {
                    SootMethod targetMethod = Helper.methodInUnit(unit);
                    if (targetMethod == null)
                        continue;

                    if (!cg.hasNode(targetMethod))
                        cg.addNode(targetMethod);

                    Set<SootClass> instantiatedClasses = Helper.instantiatedClasses(srcMethod.getDeclaringClass());
                    Set<SootClass> classes = Helper.implementingClass(hierarchy, targetMethod);
                    instantiatedClasses.retainAll(classes);

                    Set<SootMethod> rtaMethod = instantiatedClasses.stream()
                            .map(c -> c.getMethod(targetMethod.getSubSignature()))
                            .collect(Collectors.toSet());

                    for (SootMethod method : rtaMethod) {
                        if (!cg.hasNode(method))
                            cg.addNode(method);

                        if (!cg.hasEdge(srcMethod, method)) {
                            cg.addEdge(srcMethod, method);
                            queue.add(method);
                        }
                    }
                }
            }
        }
    }
}
