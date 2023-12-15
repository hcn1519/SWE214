package analysis;

import java.util.*;
import java.util.stream.Collectors;
import java.lang.Integer;

import com.google.common.collect.Sets;
import heros.DefaultSeeds;
import heros.EdgeFunction;
import heros.EdgeFunctions;
import heros.FlowFunction;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import heros.JoinLattice;
import heros.edgefunc.AllTop;
import heros.edgefunc.EdgeIdentity;
import heros.flowfunc.Identity;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.ide.DefaultJimpleIDETabulationProblem;

import static java.lang.Integer.*;

public class IDELinearConstantAnalysisProblem extends DefaultJimpleIDETabulationProblem<Local, Integer, InterproceduralCFG<Unit, SootMethod>> {

    static Integer noInformationValue = MAX_VALUE;
    static Integer overApproximatedValue = MIN_VALUE;

    protected InterproceduralCFG<Unit, SootMethod> icfg;

    public IDELinearConstantAnalysisProblem(InterproceduralCFG<Unit, SootMethod> icfg) {
        super(icfg);
        this.icfg = icfg;
    }

    @Override
    protected EdgeFunction<Integer> createAllTopFunction() {
        // TODO: Implement this function to return a special EdgeFunction that
        // represents 'no information' at all, that is used to initialize the
        // data-flow fact's values.
        return new AllTop<>(IDELinearConstantAnalysisProblem.noInformationValue);
    }

    // TODO: Implement this JoinLattice factory function, to return the lattice
    // for your data-flow analysis. The JoinLattice implementation states what
    // the top and bottom element are in your analysis's underlying lattice.
    // Additionally it states how to join two values in the lattice.
    // It probably makes sense to have an additional global variable in this
    // description class that represents the BOTTOM element; that will surely
    // become handy for the implementation of the EdgeFunctions.
    @Override
    protected JoinLattice<Integer> createJoinLattice() {

        return new JoinLattice<Integer>() {
            @Override
            public Integer topElement() {
                return IDELinearConstantAnalysisProblem.noInformationValue;
            }

            @Override
            public Integer bottomElement() {
                return IDELinearConstantAnalysisProblem.overApproximatedValue;
            }

            @Override
            public Integer join(Integer left, Integer right) {
                return min(left, right);
            }
        };
    }

    private Set<Value> valuesIn(Value value) {
        return value.getUseBoxes()
                .stream()
                .map(ValueBox::getValue)
                .collect(Collectors.toSet());
    }

    private boolean canBeEvaluatedToConstant(Set<Value> values, Local fact) {
        for (Value value : values) {
            if (!(value instanceof Constant) && !fact.equals(value)) {
                return false;
            }
        }
        return true;
    }

    // TODO: You have to implement the FlowFunctions interface.
    // This is very similar to the IFDS analysis, but this time your just use
    // Local as type of the data-flow facts. Do not worry about a Local's value
    // here (the EdgeFunctions will take care of this job), just generate and
    // kill constant Locals when adequate.
    @Override
    protected FlowFunctions<Unit, Local, SootMethod> createFlowFunctionsFactory() {

        return new FlowFunctions<Unit, Local, SootMethod>() {
            @Override
            public FlowFunction<Local> getNormalFlowFunction(Unit curr, Unit succ) {
                // TODO: Implement this flow function factory to obtain an intra-procedural data-flow analysis.
                return new FlowFunction<Local>() {
                    @Override
                    public Set<Local> computeTargets(Local fact) {
                        Set<Local> out = Sets.newHashSet();
                        out.add(fact);

                        try {
                            if (curr instanceof AssignStmt) {
                                AssignStmt assignStmt = (AssignStmt) curr;
                                Value leftOp = assignStmt.getLeftOp();
                                Value rightOp = assignStmt.getRightOp();

                                if (!(leftOp instanceof Local))
                                    return out;

                                Local leftLocal = (Local) leftOp;
                                if (fact.equals(zeroValue())) {
                                    if (rightOp instanceof Constant)
                                        out.add(leftLocal);

                                    return out;
                                }

                                // non zero
                                if (rightOp instanceof Constant)
                                    return out;

                                Set<Value> valuesInRightOp = valuesIn(rightOp);
                                if (canBeEvaluatedToConstant(valuesInRightOp, fact)) {
                                    out.add(leftLocal);
                                    return out;
                                }
                                return out;
                            }
                            return out;
                        } finally {
//                            System.out.println("Flow Normal " + curr + ", fact " + fact + ", out " + out);
                        }
                    }
                };
            }

            @Override
            public FlowFunction<Local> getCallFlowFunction(Unit callStmt, SootMethod dest) {
                // TODO: Implement this flow function factory to map the actual into the formal arguments.
                // Caution, actual parameters may be integer literals as well.
                return new FlowFunction<Local>() {
                    @Override
                    public Set<Local> computeTargets(Local fact) {
                        Set<Local> out = Sets.newHashSet();
                        try {
                            if (!(callStmt instanceof Stmt))
                                return out;

                            Stmt callSiteStmt = (Stmt) callStmt;
                            InvokeExpr invokeExpr = callSiteStmt.getInvokeExpr();

                            List<Value> args = invokeExpr.getArgs();
                            List<Local> params = dest.getActiveBody().getParameterLocals();
                            for (int i = 0; i < invokeExpr.getArgCount(); i++) {
                                Value argument = args.get(i);
                                if (fact.equals(argument)) {
                                    out.add(params.get(i));
                                }
                                if (fact.equals(zeroValue()) && argument instanceof IntConstant) {
                                    out.add(params.get(i));
                                }
                            }
                            return out;
                        } finally {
//                            System.out.println("Flow CallFlow " + callStmt + ", fact " + fact + ", out " + out);
                        }
                    }
                };
            }

            @Override
            public FlowFunction<Local> getReturnFlowFunction(Unit callSite, SootMethod calleeMethod, Unit exitStmt, Unit returnSite) {
                // TODO: Map the return value back into the caller's context if applicable.
                // Since Java has pass-by-value semantics for primitive data types, you do not have to map the formals
                // back to the actuals at the exit of the callee.
                return new FlowFunction<Local>() {
                    @Override
                    public Set<Local> computeTargets(Local fact) {
                        Set<Local> out = Sets.newHashSet();
                        try {
                            if (exitStmt instanceof ReturnStmt && callSite instanceof AssignStmt) {
                                AssignStmt callsiteAssignStmt = (AssignStmt) callSite;
                                Value callsiteLeftOp = callsiteAssignStmt.getLeftOp();
                                Value retOp = ((ReturnStmt)exitStmt).getOp();

                                if (retOp instanceof Constant) {
                                    if (fact.equals(zeroValue())) {
                                        out.add((Local) callsiteLeftOp);
                                    }
                                } else if (fact.equals(zeroValue()) || fact.equals(retOp)) {
                                    out.add((Local)callsiteLeftOp);
                                }

                                if (retOp instanceof Local) {
                                    out.add((Local)retOp);
                                }
                            }
                            return out;
                        } finally {
//                            System.out.println("Flow Return " + callSite + ", fact " + fact + ", out " + out);
                        }
                    }
                };
            }

            @Override
            public FlowFunction<Local> getCallToReturnFlowFunction(Unit callSite, Unit returnSite) {
                // TODO: getCallToReturnFlowFunction can be left to return id in many analysis; this time as well?
                return Identity.v();
            }
        };
    }

    // TODO: You have to implement the EdgeFunctions interface.
    // The EdgeFunctions take care of the actual value computation within this
    // linear constant propagation. An EdgeFunction is basically the
    // non-evaluated function representation of a constant Integer value
    // (or better its computation).
    // Similar to the FlowFunctions you may return different EdgeFunctions
    // depending on the current statement you are looking at.
    // An EdgeFunction describes an IDE lambda function on an exploded
    // super-graph edge from 'srcNode' to 'tgtNode', for instance, when looking
    // at 'getNormalEdgeFunction'. Do you have to implement all EdgeFunction
    // factory methods for the linear constant propagation?
    // Before you start, let us clarify the EdgeFunction interface:
    //        public interface EdgeFunction<V> {
    //          // This is where the magic happens and the most important
    //          // function of this interface. In compute targets your encode
    //          // the actual lambda function that describes what operation is
    //          // performed on an incoming Integer. This function can for
    //          // instance return a number, pass it as identity or perform
    //          // furth arithmetic operations on it.
    //          V computeTarget(V source);
    //          // In composeWith you are able to describe how two EdgeFunctions
    //          // can be composed with each other. You probably would like to
    //          // create a new class implementeing the EdgeFunction interface
    //          // and is able compose two EdgeFunctions.
    //          EdgeFunction<V> composeWith(EdgeFunction<V> secondFunction);
    //          // As the name suggests this function states how two
    //          // EdgeFunctions have to be joined. Remember that EdgeFunctions
    //          // are non-evaluated constant values.
    //          EdgeFunction<V> joinWith(EdgeFunction<V> otherFunction);
    //          // This function tells if 'this' EdgeFunction and the 'other'
    //          // EdgeFunction are equal.
    //          public boolean equalTo(EdgeFunction<V> other);
    //        }
    // Happy data-flow analysis ;-)
    @Override
    protected EdgeFunctions<Unit, Local, SootMethod, Integer> createEdgeFunctionsFactory() {

        return new EdgeFunctions<Unit, Local, SootMethod, Integer>() {
            @Override
            public EdgeFunction<Integer> getNormalEdgeFunction(Unit src, Local srcNode, Unit tgt, Local tgtNode) {
                try {
                    if (src instanceof AssignStmt) {
                        AssignStmt assign = (AssignStmt) src;
                        Value leftOp = assign.getLeftOp();
                        Value rightOp = assign.getRightOp();

                        if (srcNode.equals(zeroValue()) && tgtNode.equals(leftOp)) {
                            if (rightOp instanceof IntConstant) {
                                return new IntConstantEdgeFunction(((IntConstant) rightOp).value, src);
                            }
                        }

                        if (!srcNode.equals(zeroValue()) && srcNode.equals(leftOp) && rightOp instanceof Constant) {
                            return new IntConstantEdgeFunction(((IntConstant) rightOp).value, src);
                        }

                        if (!srcNode.equals(zeroValue()) && tgtNode.equals(leftOp) && rightOp instanceof BinopExpr) {
                            BinopExpr rightBinopExpr = (BinopExpr) rightOp;

                            if (rightBinopExpr.getOp1().equals(srcNode) || rightBinopExpr.getOp2().equals(srcNode)) {
                                return new BinaryOperationEdgeFunction(rightBinopExpr, src);
                            }
                        }
                    }
                    return EdgeIdentity.v();
                } finally {
//                    System.out.println("Edge Normal src " + src + ", srcNode "+ srcNode + ", target " + tgt +", tgtNode "+ tgtNode);
                }
            }

            @Override
            public EdgeFunction<Integer> getCallEdgeFunction(Unit callStmt, Local srcNode, SootMethod destinationMethod, Local destNode) {
                try {
                    Stmt stmt = (Stmt) callStmt;
                    InvokeExpr invokeExpr = stmt.getInvokeExpr();

                    if (srcNode.equals(zeroValue()) && !destNode.equals(zeroValue())) {
                        int paramIdx = destinationMethod.getActiveBody().getParameterLocals().indexOf(destNode);
                        Value mappedArg = invokeExpr.getArgs().get(paramIdx);
                        if (mappedArg instanceof IntConstant) {
                            return new IntConstantEdgeFunction(((IntConstant) mappedArg).value, callStmt);
                        }
                    }

                    return EdgeIdentity.v();
                } finally {
//                    System.out.println("Edge CallEdge " + callStmt + ", srcNode "+ srcNode + ", destinationMethod " + destinationMethod +", destNode "+ destNode);
                }
            }

            @Override
            public EdgeFunction<Integer> getReturnEdgeFunction(Unit callSite, SootMethod calleeMethod, Unit exitStmt, Local exitNode, Unit returnSite, Local retNode) {
                try {
                    if (exitNode.equals(zeroValue()) && !retNode.equals(zeroValue())) {
                        ReturnStmt returnStmt = (ReturnStmt) exitStmt;
                        Value v = returnStmt.getOp();
                        if (v instanceof IntConstant) {
                            return new IntConstantEdgeFunction(((IntConstant) v).value, callSite);
                        }
                    }
                    return EdgeIdentity.v();
                } finally {
//                    System.out.println("Edge Return " + callSite +", returnSite "+ returnSite + ", returnNode " + retNode);
                }
            }

            @Override
            public EdgeFunction<Integer> getCallToReturnEdgeFunction(Unit callStmt, Local callNode, Unit returnSite, Local returnSideNode) {
                return EdgeIdentity.v();
            }
        };
    }

    @Override
    protected JimpleLocal createZeroValue() {
        return new JimpleLocal("<<zero>>", NullType.v());
    }

    @Override
    public Map<Unit, Set<Local>> initialSeeds() {
        for (SootClass c : Scene.v().getApplicationClasses()) {
            for (SootMethod m : c.getMethods()) {
                if (!m.hasActiveBody()) {
                    continue;
                }
                if (m.getName().equals("entryPoint")) {
                    return DefaultSeeds.make(Collections.singleton(m.getActiveBody().getUnits().getFirst()), zeroValue());
                }
            }
        }
        throw new IllegalStateException("scene does not contain 'entryPoint'");
    }
}

class IntConstantEdgeFunction implements EdgeFunction<java.lang.Integer> {

    Integer constant;
    Unit src;
    Local srcLeftOp;

    public IntConstantEdgeFunction(Integer constant, Unit src) {
        this.constant = constant;
        this.src = src;
        this.srcLeftOp = (Local) ((AssignStmt) src).getLeftOp();
    }
    @Override
    public Integer computeTarget(Integer integer) {
        return this.constant;
    }

    @Override
    public EdgeFunction<Integer> composeWith(EdgeFunction<Integer> secondFunction) {
        if (secondFunction.equals(EdgeIdentity.v())) {
            return this;
        }
        if (secondFunction instanceof BinaryOperationEdgeFunction) {
            BinaryOperationEdgeFunction other = (BinaryOperationEdgeFunction) secondFunction;
            Integer newI = other.computeTarget(this.constant);
            return new IntConstantEdgeFunction(newI, other.src);
        }
        if (secondFunction instanceof IntConstantEdgeFunction) {
            return secondFunction;
        }
        return this;
    }

    @Override
    public EdgeFunction<Integer> joinWith(EdgeFunction<Integer> otherFunction) {
        if (otherFunction.equals(EdgeIdentity.v())) {
            return this;
        }
        if (otherFunction instanceof IntConstantEdgeFunction) {
            return otherFunction;
        }
        return this;
    }

    @Override
    public boolean equalTo(EdgeFunction<Integer> other) {
        return this.equals(other);
    }
}

class BinaryOperationEdgeFunction implements EdgeFunction<Integer> {
    BinopExpr binopExpr;
    Unit src;
    Local srcLeftOp;

    public BinaryOperationEdgeFunction(BinopExpr binopExpr, Unit src) {
        this.binopExpr = binopExpr;
        this.src = src;
        this.srcLeftOp = (Local) ((AssignStmt) src).getLeftOp();
    }
    @Override
    public Integer computeTarget(Integer integer) {
        Value leftValue = binopExpr.getOp1();
        Value rightValue = binopExpr.getOp2();

        Integer result = null;
        try {
            Integer leftInt = null;
            if (leftValue instanceof IntConstant) {
                leftInt = ((IntConstant) leftValue).value;
            } else {
                leftInt = integer;
            }

            Integer rightInt = null;
            if (rightValue instanceof IntConstant) {
                rightInt = ((IntConstant) rightValue).value;
            } else {
                rightInt = integer;
            }

            if (leftInt == null || rightInt == null)
                return IDELinearConstantAnalysisProblem.overApproximatedValue;

            if (binopExpr instanceof AddExpr) {
                result = leftInt + rightInt;
            } else if (binopExpr instanceof MulExpr) {
                result = leftInt * rightInt;
            } else if (binopExpr instanceof SubExpr) {
                result = leftInt - rightInt;
            } else if (binopExpr instanceof DivExpr) {
                result = leftInt / rightInt;
            } else if (binopExpr instanceof RemExpr) {
                result = leftInt % rightInt;
            }
            return result;
        } finally {
//            System.out.println("Bin compute " + result + ", integer " + integer);
        }
    }

    @Override
    public EdgeFunction<Integer> composeWith(EdgeFunction<Integer> secondFunction) {
        if (secondFunction.equals(EdgeIdentity.v())) {
            return this;
        }
        return secondFunction.composeWith(this);
    }

    @Override
    public EdgeFunction<Integer> joinWith(EdgeFunction<Integer> otherFunction) {
        if (otherFunction.equals(EdgeIdentity.v())) {
            return this;
        }
        return this;
    }

    @Override
    public boolean equalTo(EdgeFunction<Integer> edgeFunction) {
        return this.equals(edgeFunction);
    }
}
