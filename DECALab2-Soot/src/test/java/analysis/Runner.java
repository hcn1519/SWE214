package analysis;

import analysis.exercise3.VTAAlgorithm;
import base.TestSetup;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootMethod;
import soot.Transformer;

import java.util.Map;

public class Runner  extends TestSetup {
    private Scene scene;
    private CallGraph cg;
    private SootMethod scenarioMain;

    @Override
    protected Transformer createAnalysisTransformer() {
        return new SceneTransformer() {
            @Override
            protected void internalTransform(String phaseName, Map<String, String> options) {
                //Scene.v().getApplicationClasses().stream().forEach(c -> System.out.println(c.toString()));
                //Scene.v().getEntryPoints().stream().forEach(c -> System.out.println(c.toString()));

                scene = Scene.v();
            }
        };
    }

    public void run() {
        executeStaticAnalysis();

        VTAAlgorithm vta = new VTAAlgorithm();
        vta.constructCallGraph(scene);
        cg = vta.constructCallGraph(scene);
    }
}
