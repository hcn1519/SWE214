package analysis.exercise1;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import analysis.Helper;
import soot.*;

import java.util.*;
import java.util.stream.Collectors;

public class CHAAlgorithm extends CallGraphAlgorithm {

    @Override
    protected String getAlgorithm() {
        return "CHA";
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

                    Set<SootClass> classes = Helper.implementingClass(hierarchy, targetMethod);
                    String targetSignature = targetMethod.getSubSignature();
                    Set<SootMethod> chaMethods = classes.stream()
                            .map(c -> c.getMethod(targetSignature))
                            .collect(Collectors.toSet());

                    chaMethods.add(targetMethod);
                    for (SootMethod method : chaMethods) {
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