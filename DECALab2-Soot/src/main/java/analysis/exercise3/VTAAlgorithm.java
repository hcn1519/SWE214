package analysis.exercise3;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import analysis.exercise1.CHAAlgorithm;
import org.graphstream.algorithm.TarjanStronglyConnectedComponents;
import org.graphstream.graph.Edge;
import org.graphstream.graph.Graph;
import org.graphstream.graph.Node;
import org.graphstream.graph.implementations.MultiGraph;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JReturnStmt;

import java.util.*;
import java.util.stream.Collectors;

public class VTAAlgorithm extends CallGraphAlgorithm {

    private final Logger log = LoggerFactory.getLogger("VTA");

    @Override
    protected String getAlgorithm() {
        return "VTA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph cg) {
        CallGraph initialCallGraph = new CHAAlgorithm().constructCallGraph(scene);
        TypeAssignmentGraph typeAssignmentGraph = new TypeAssignmentGraph();
        List<SootMethod> entries = this.getEntryPoints(scene).collect(Collectors.toList());

        // 1. Build Initial TypeAssignmentGraph
        for (SootMethod entry : entries) {
            this.buildTypeAssignmentGraph(scene, entry, initialCallGraph, typeAssignmentGraph);
        }
        // 2. Propagate type in TypeAssignmentGraph
        this.propagateType(typeAssignmentGraph);

//        typeAssignmentGraph.draw();
        System.out.println("Tagged Nodes " + typeAssignmentGraph.getTaggedNodes());

//        // 3. Resolve Strong connected components
//        for (Pair<Value, Set<SootClass>> node : typeAssignmentGraph.getTaggedNodes()) {
//            Object scc = typeAssignmentGraph.getSccIndex(node.first);
//            System.out.println("scc " + scc);
//        }

        // 4. create pruned call graph
        // Infer what types the objects involved in a call may have
        // Prune calls that are infeasible based on the inferred types
        for (SootMethod entry : entries) {
            Queue<SootMethod> queue = new ArrayDeque<>();
            queue.add(entry);

            while (!queue.isEmpty()) {
                SootMethod srcMethod = queue.poll();
                if (!cg.hasNode(srcMethod))
                    cg.addNode(srcMethod);

                Set<SootMethod> targets = initialCallGraph.edgesOutOf(srcMethod);
                for (SootMethod target : targets) {
                    if (!isFeasibleMethod(typeAssignmentGraph, target))
                        continue;

                    if (!cg.hasNode(target))
                        cg.addNode(target);
                    if (!cg.hasEdge(srcMethod, target)) {
                        cg.addEdge(srcMethod, target);
                        queue.add(target);
                    }
                }
            }
        }
    }

    private void buildTypeAssignmentGraph(Scene scene, SootMethod entry, CallGraph initialCallGraph, TypeAssignmentGraph typeAssignmentGraph) {
        Queue<SootMethod> queue = new ArrayDeque<>();
        queue.add(entry);

        while (!queue.isEmpty()) {
            SootMethod srcMethod = queue.poll();
            if (!srcMethod.hasActiveBody())
                continue;

            Body body = srcMethod.getActiveBody();
            for (Unit unit : body.getUnits()) {
                if ((unit instanceof JAssignStmt)) {
                    JAssignStmt assignStmt = (JAssignStmt) unit;
                    Value lhs = assignStmt.getLeftOp();
                    Value rhs = assignStmt.getRightOp();
                    typeAssignmentGraph.addNode(lhs);

                    if (rhs instanceof JNewExpr) {
                        JNewExpr newExpr = (JNewExpr) rhs;
                        SootClass classTag = scene.getSootClass(newExpr.getType().toString());
                        typeAssignmentGraph.tagNode(lhs, classTag);
                    } else if (rhs instanceof InvokeExpr) {
                        InvokeExpr invokeExpr = (InvokeExpr) rhs;
                        this.addEdgeToArgument(typeAssignmentGraph, invokeExpr);
                        SootMethod method = invokeExpr.getMethod();
                        SootClass classTag = this.returnType(scene, method);
                        typeAssignmentGraph.tagNode(lhs, classTag);

                        queue.addAll(initialCallGraph.edgesOutOf(method));
                    } else {
                        if (!(rhs instanceof Constant)) {
                            typeAssignmentGraph.addNode(rhs);
                            typeAssignmentGraph.addEdge(rhs, lhs);
                        }
                    }
                } else if (unit instanceof JInvokeStmt) {
                    JInvokeStmt invokeStmt = (JInvokeStmt) unit;
                    InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
                    this.addEdgeToArgument(typeAssignmentGraph, invokeExpr);
                    SootMethod method = invokeExpr.getMethod();

                    queue.addAll(initialCallGraph.edgesOutOf(method));
                }
            }
        }
    }

    // Add edge between method in InvokeExpr to arguments
    private void addEdgeToArgument(TypeAssignmentGraph typeAssignmentGraph, InvokeExpr invokeExpr) {
        List<Value> args = invokeExpr.getArgs();
        SootMethod method = invokeExpr.getMethod();

        for (int i = 0; i < args.size(); i++) {
            Value arg = args.get(i);
            if (!(arg instanceof Constant) && (method.hasActiveBody())) {
                List<Value> parameterRefs = method.getActiveBody().getParameterRefs();

                for (Value value : parameterRefs) {
                    ParameterRef parameterRef = (ParameterRef) value;
                    if (i == parameterRef.getIndex()) {
                        typeAssignmentGraph.addNode(arg);
                        typeAssignmentGraph.addNode(parameterRef);
                        typeAssignmentGraph.addEdge(arg, value);
                    }
                }
            }
        }
    }

    // Search concrete return type of the method if possible.
    private SootClass returnType(Scene scene, SootMethod method) {
        if (!method.hasActiveBody()) {
            return scene.getSootClass(method.getReturnType().toString());
        }

        Body body = method.getActiveBody();
        HashMap<Value, SootClass> localMap = new HashMap<>();

        for (Unit unit : body.getUnits()) {
            if (unit instanceof JAssignStmt) {
                JAssignStmt assignStmt = (JAssignStmt) unit;
                Value lhs = assignStmt.getLeftOp();
                Value rhs = assignStmt.getRightOp();

                if (rhs instanceof JNewExpr) {
                    JNewExpr newExpr = (JNewExpr) rhs;
                    SootClass classTag = scene.getSootClass(newExpr.getType().toString());
                    localMap.put(lhs, classTag);
                } else if (rhs instanceof InvokeExpr) {
                    InvokeExpr invokeExpr = (InvokeExpr) rhs;
                    SootClass classTag = this.returnType(scene, invokeExpr.getMethod());
                    localMap.put(lhs, classTag);
                }
            }
        }
        for (Unit unit : body.getUnits()) {
            if (unit instanceof JReturnStmt) {
                JReturnStmt returnStmt = (JReturnStmt) unit;
                Value returnOP = returnStmt.getOp();
                return localMap.get(returnOP);
            }
        }
        return scene.getSootClass(method.getReturnType().toString());
    }

    // Propagate type iterating through Type Assignment Graph
    private void propagateType(TypeAssignmentGraph typeAssignmentGraph) {
        Queue<Pair<Value, Set<SootClass>>> queue = new ArrayDeque<>();
        for (Pair<Value, Set<SootClass>> pair : typeAssignmentGraph.getTaggedNodes()) {
            queue.add(pair);

            while (!queue.isEmpty()) {
                Pair<Value, Set<SootClass>> src = queue.poll();
                Set<Value> targets = typeAssignmentGraph.getTargetsFor(src.first);

                for (Value target : targets) {
                    for (SootClass cls: src.second) {
                        typeAssignmentGraph.tagNode(target, cls);
                    }
                    queue.add(new Pair<Value, Set<SootClass>>(target, typeAssignmentGraph.getNodeTags(target)));
                }
            }
        }
    }

    // Decide whether method is reachable using Variable Type graph
    private boolean isFeasibleMethod(TypeAssignmentGraph typeAssignmentGraph, SootMethod method) {
        SootClass destClass = method.getDeclaringClass();
        Queue<Value> queue = new ArrayDeque<>();

        // Set up entries
        for (Pair<Value, Set<SootClass>> pair : typeAssignmentGraph.getTaggedNodes()) {
            if (pair.second.contains(destClass)) {
                queue.add(pair.first);
            }
        }

        while (!queue.isEmpty()) {
            Value srcValue = queue.poll();
            if (typeAssignmentGraph.getNodeTags(srcValue).contains(destClass))
                return true;
            queue.addAll(typeAssignmentGraph.getTargetsFor(srcValue));
        }
        return false;
    }

    /**
     * You can use this class to represent your type assignment graph.
     * We do not use this data structure in tests, so you are free to use something else.
     * However, we use this data structure in our solution and it instantly supports collapsing strong-connected components.
     */
    private class TypeAssignmentGraph {
        private final Graph graph;
        private TarjanStronglyConnectedComponents tscc = new TarjanStronglyConnectedComponents();

        public TypeAssignmentGraph() {
            this.graph = new MultiGraph("tag");
        }

        private boolean containsNode(Value value) {
            return graph.getNode(createId(value)) != null;
        }

        private boolean containsEdge(Value source, Value target) {
            return graph.getEdge(createId(source) + "-" + createId(target)) != null;
        }

        private String createId(Value value) {
            if (value instanceof FieldRef)
                return value.toString();
            return Integer.toHexString(System.identityHashCode(value));
        }

        public void addNode(Value value) {
            if (!containsNode(value)) {
                Node node = graph.addNode(createId(value));
                node.setAttribute("value", value);
                node.setAttribute("ui.label", value);
                node.setAttribute("tags", new HashSet<SootClass>());
            }
        }

        public void tagNode(Value value, SootClass classTag) {
            if (containsNode(value))
                getNodeTags(value).add(classTag);
        }

        public Set<Pair<Value, Set<SootClass>>> getTaggedNodes() {
            return graph.getNodeSet().stream()
                    .map(n -> new Pair<Value, Set<SootClass>>(n.getAttribute("value"), (Set<SootClass>) n.getAttribute("tags")))
                    .filter(p -> p.second.size() > 0)
                    .collect(Collectors.toSet());
        }

        public Set<SootClass> getNodeTags(Value val) {
            return ((Set<SootClass>) graph.getNode(createId(val)).getAttribute("tags"));
        }

        public void addEdge(Value source, Value target) {
            if (!containsEdge(source, target)) {
                Node sourceNode = graph.getNode(createId(source));
                Node targetNode = graph.getNode(createId(target));
                if (sourceNode == null || targetNode == null)
                    log.error("Could not find one of the nodes. Source: " + sourceNode + " - Target: " + targetNode);
                graph.addEdge(createId(source) + "-" + createId(target),
                        sourceNode,
                        targetNode, true);
            }

        }

        public Set<Value> getTargetsFor(Value initialNode) {
            if (!containsNode(initialNode)) return Collections.emptySet();
            Node source = graph.getNode(createId(initialNode));
            Collection<Edge> edges = source.getLeavingEdgeSet();
            return edges.stream()
                    .map(e -> (Value) e.getTargetNode().getAttribute("value"))
                    .collect(Collectors.toSet());
        }

        /**
         * Use this method to start the SCC computation.
         */
        public void annotateScc() {
            tscc.init(graph);
            tscc.compute();
        }

        /**
         * Retrieve the index assigned by the SCC algorithm
         * @param value
         * @return
         */
        public Object getSccIndex(Value value) {
            if(!containsNode(value))
                return null;
            return graph.getNode(createId(value)).getAttribute(tscc.getSCCIndexAttribute());
        }

        /**
         * Use this method to inspect your type assignment graph
         */
        public void draw() {
            graph.display();
        }
    }

    private class Pair<A, B> {
        final A first;
        final B second;

        public Pair(A first, B second) {
            this.first = first;
            this.second = second;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Pair<?, ?> pair = (Pair<?, ?>) o;

            if (first != null ? !first.equals(pair.first) : pair.first != null) return false;
            return second != null ? second.equals(pair.second) : pair.second == null;
        }

        @Override
        public int hashCode() {
            int result = first != null ? first.hashCode() : 0;
            result = 31 * result + (second != null ? second.hashCode() : 0);
            return result;
        }

        @Override
        public String toString() {
            return "(" + first +
                    ", " + second +
                    ')';
        }
    }

}
