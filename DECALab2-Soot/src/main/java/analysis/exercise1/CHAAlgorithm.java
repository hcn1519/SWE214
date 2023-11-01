package analysis.exercise1;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import soot.Local;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.VirtualInvokeExpr;

public class CHAAlgorithm extends CallGraphAlgorithm {

    @Override
    protected String getAlgorithm() {
        return "CHA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph cg) {
        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you

    }

}
