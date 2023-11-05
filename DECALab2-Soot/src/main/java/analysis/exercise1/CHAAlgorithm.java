package analysis.exercise1;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import java.util.*;
import java.util.List;
import java.util.stream.Collectors;

public class CHAAlgorithm extends CallGraphAlgorithm {

    @Override
    protected String getAlgorithm() {
        return "CHA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph cg) {
        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you

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
                    SootMethod targetMethod = this.targetMethod(unit);
                    if (targetMethod == null)
                        continue;

                    if (!cg.hasNode(targetMethod))
                        cg.addNode(targetMethod);

                    List<SootClass> classes = this.implementingClass(hierarchy, targetMethod);
                    String targetSignature = targetMethod.getSubSignature();
                    List<SootMethod> chaMethods = classes.stream()
                            .map(c -> c.getMethod(targetSignature))
                            .collect(Collectors.toList());

                    chaMethods.add(targetMethod);
                    for (SootMethod method : chaMethods) {
                        if (!cg.hasNode(method))
                            cg.addNode(method);

                        if (!cg.hasEdge(srcMethod, method)) {
                            cg.addEdge(srcMethod, method);
                            queue.add(targetMethod);
                        }
                    }
                }
            }
        }
    }

    private SootMethod targetMethod(Unit unit) {
        if (unit instanceof soot.jimple.internal.JAssignStmt) {
            JAssignStmt assignStmt = (JAssignStmt) unit;
            if (assignStmt.containsInvokeExpr())
                return assignStmt.getInvokeExpr().getMethod();

        } else if (unit instanceof soot.jimple.internal.JInvokeStmt) {
            JInvokeStmt invokeStmt = (JInvokeStmt) unit;
            InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
            return invokeExpr.getMethod();
        }
        return null;
    }

    private List<SootClass> implementingClass(Hierarchy hierarchy, SootMethod method) {
        SootClass cls = method.getDeclaringClass();
        if (cls.isInterface())
            return hierarchy.getImplementersOf(cls);
        return new ArrayList<>(Collections.singleton(cls));
    }
}