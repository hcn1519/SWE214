package analysis;

import soot.*;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;

import java.util.HashSet;
import java.util.Set;

public class Helper {
    public static SootMethod targetMethod(Unit unit) {
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

    public static Set<SootClass> implementingClass(Hierarchy hierarchy, SootMethod method) {
        SootClass cls = method.getDeclaringClass();
        if (cls.isInterface()) {
            return new HashSet<>(hierarchy.getImplementersOf(cls));
        }
        Set<SootClass> result = new HashSet<>();
        result.add(cls);
        return result;
    }

    public static Set<SootClass> instantiatedClasses(SootClass targetClass) {
        Set<SootClass> res = new HashSet<>();

        for (SootField field : targetClass.getFields()) {
            Type fieldType = field.getType();

            if (fieldType instanceof RefType) {
                SootClass referencedClass = ((RefType) fieldType).getSootClass();
                res.add(referencedClass);
            }
        }

        for (SootMethod method : targetClass.getMethods()) {
            if (!method.hasActiveBody())
                continue;
            Body methodBody = method.retrieveActiveBody();

            for (Unit unit : methodBody.getUnits()) {
                Stmt stmt = (Stmt) unit;

                if (stmt.containsInvokeExpr()) {
                    SootMethod targetMethod = stmt.getInvokeExpr().getMethod();
                    SootClass referencedClass = targetMethod.getDeclaringClass();
                    res.add(referencedClass);
                }
            }
        }
        return res;
    }
}
