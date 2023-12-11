package analysis;

import java.util.*;
import java.util.stream.Collectors;

import com.google.common.collect.Sets;
import heros.DefaultSeeds;
import heros.FlowFunction;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import heros.solver.Pair;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.ide.DefaultJimpleIFDSTabulationProblem;

public class IFDSLinearConstantAnalysisProblem extends DefaultJimpleIFDSTabulationProblem<Pair<Local, Integer>, InterproceduralCFG<Unit, SootMethod>> {

    protected final static int LOWER_BOUND = -1000;

    protected final static int UPPER_BOUND = 1000;

    protected InterproceduralCFG<Unit, SootMethod> icfg;

    public IFDSLinearConstantAnalysisProblem(InterproceduralCFG<Unit, SootMethod> icfg) {
        super(icfg);
        this.icfg = icfg;
    }

    @Override
    public Map<Unit, Set<Pair<Local, Integer>>> initialSeeds() {
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

    private boolean evalIfConditionIfPossible(IfStmt ifStmt, Pair<Local, Integer> fact) {

        Value ifStmtCondition = ifStmt.getCondition();
        Set<Value> values = ifStmtCondition.getUseBoxes()
                .stream()
                .map(ValueBox::getValue)
                .collect(Collectors.toSet());

        if (!values.contains(fact.getO1()))
            return false;

        if (ifStmtCondition instanceof ConditionExpr) {
            ConditionExpr conditionExpr = (ConditionExpr) ifStmtCondition;
            Integer res = evalBinaryExpression(conditionExpr, fact);

            if (res == null)
                return false;
            return res == 1;
        }

        return true;
    }
    private Integer evalBinaryExpression(BinopExpr expr, Pair<Local, Integer> fact) {
        Value leftValue = expr.getOp1();
        Value rightValue = expr.getOp2();

        Integer leftInt = null;
        if (leftValue instanceof IntConstant) {
            leftInt = ((IntConstant) leftValue).value;
        } else if (fact.getO1().equals(leftValue)) {
            leftInt = fact.getO2();
        }

        Integer rightInt = null;
        if (rightValue instanceof IntConstant) {
            rightInt = ((IntConstant) rightValue).value;
        } else if (fact.getO1().equals(rightValue)) {
            rightInt = fact.getO2();
        }

        if (leftInt == null || rightInt == null) {
            return null;
        }

        if (expr instanceof AddExpr) {
            return leftInt + rightInt;
        } else if (expr instanceof MulExpr) {
            return leftInt * rightInt;
        } else if (expr instanceof SubExpr) {
            return leftInt - rightInt;
        } else if (expr instanceof DivExpr) {
            return leftInt / rightInt;
        } else if (expr instanceof RemExpr) {
            return leftInt % rightInt;
        } else if (expr instanceof ConditionExpr) {
            if (expr.getSymbol().equals(" >= "))
                return leftInt >= rightInt ? 1 : 0;
            else if (expr.getSymbol().equals(" <= "))
                return leftInt <= rightInt ? 1 : 0;
            else if (expr.getSymbol().equals(" > "))
                return leftInt > rightInt ? 1 : 0;
            else if (expr.getSymbol().equals(" < "))
                return leftInt < rightInt ? 1 : 0;
            else if (expr.getSymbol().equals(" == "))
                return leftInt.equals(rightInt) ? 1 : 0;
        }
        return null;
    }

    private Set<Pair<Local, Integer>> evalAssignment(AssignStmt assignStmt, Pair<Local, Integer> fact) {
        Set<Pair<Local, Integer>> out = Sets.newHashSet();
        Value leftOp = assignStmt.getLeftOp();
        Value rightOp = assignStmt.getRightOp();

        if (leftOp instanceof Local) {
            Local leftLocal = (Local)leftOp;

            // case1 stmt i = not integer, fact<zero>
            if (!(rightOp instanceof IntConstant)) {

                if (rightOp instanceof BinopExpr) {
                    BinopExpr rightBinopExpr = (BinopExpr) rightOp;
                    Integer rightInteger = evalBinaryExpression(rightBinopExpr, fact);
                    out.add(fact);

                    if (rightInteger != null) {
                        out.add(new Pair<>(leftLocal, rightInteger));
                        return out;
                    }
                }
                return out;
            }

            int rightInt = ((IntConstant) rightOp).value;

            // case1 stmt i = 200, fact<zero>
            // case2 stmt i = 200, fact<i, 100>
            if (fact.equals(zeroValue()) || fact.getO1().equals(leftLocal))
                return Collections.singleton(new Pair<>(leftLocal, rightInt));

            // case3 stmt i = 200, fact<j, 100>
            if (!fact.getO1().equals(leftLocal)) // stmt j = 200, fact<i, 200>
                return Collections.singleton(fact);
        }
        return out;
    }

    // TODO: You have to implement the FlowFunctions interface.
    // Use Pair<Local, Integer> as type for the data-flow facts.
    @Override
    protected FlowFunctions<Unit, Pair<Local, Integer>, SootMethod> createFlowFunctionsFactory() {
        return new FlowFunctions<Unit, Pair<Local, Integer>, SootMethod>() {
            @Override
            public FlowFunction<Pair<Local, Integer>> getNormalFlowFunction(Unit curr, Unit next) {
                // TODO: Implement this flow function factory to obtain an intra-procedural data-flow analysis.
                return new FlowFunction<Pair<Local, Integer>>() {
                    @Override
                    public Set<Pair<Local, Integer>> computeTargets(Pair<Local, Integer> fact) {
                        Set<Pair<Local, Integer>> out = Sets.newHashSet();
                        out.add(fact);

                        try {
                            // Loop condition handling
                            if (curr instanceof GotoStmt) {
                                GotoStmt gotoStmt = (GotoStmt) curr;

                                if (gotoStmt.getTarget() == next) {
                                    if (next instanceof IfStmt) {
                                        IfStmt ifStmt = (IfStmt) next;
                                        Stmt targetStmt = ifStmt.getTarget();

                                        if (fact.getO2() > UPPER_BOUND || fact.getO2() < LOWER_BOUND) {
                                            return Collections.emptySet();
                                        }

                                        if (evalIfConditionIfPossible(ifStmt, fact)) {
                                            if (targetStmt instanceof AssignStmt) {
                                                out.addAll(evalAssignment((AssignStmt) targetStmt, fact));
                                                return out;
                                            }
                                        }
                                        return out;
                                    }
                                }
                            }
                            // If condition handling
                            if (curr instanceof IfStmt) {
                                IfStmt ifStmt = (IfStmt) curr;
                                Stmt targetStmt = ifStmt.getTarget();

                                if (evalIfConditionIfPossible(ifStmt, fact)) {
                                    if (targetStmt instanceof AssignStmt) {
                                        out.addAll(evalAssignment((AssignStmt) targetStmt, fact));
                                        return out;
                                    }
                                }
                                return out;
                            }

                            // Assignment handling
                            if (curr instanceof AssignStmt) {
                                out.addAll(evalAssignment((AssignStmt) curr, fact));
                                return out;
                            }
                            return out;
                        } finally {
//                            System.out.println("normal curr " + curr + ", fact " + fact + ", out" + out);
                        }
                    }
                };
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getCallFlowFunction(Unit callsite, SootMethod dest) {
                // TODO: Implement this flow function factory to map the actual into the formal arguments.
                // Caution, actual parameters may be integer literals as well.
                return new FlowFunction<Pair<Local, Integer>>() {
                    @Override
                    public Set<Pair<Local, Integer>> computeTargets(Pair<Local, Integer> fact) {
                        if (fact.equals(zeroValue()))
                            return Collections.emptySet();

                        Set<Pair<Local, Integer>> out = Sets.newHashSet();
                        if (!(callsite instanceof Stmt))
                            return out;

                        Stmt callSiteStmt = (Stmt) callsite;
                        InvokeExpr invokeExpr = callSiteStmt.getInvokeExpr();

                        List<Value> args = invokeExpr.getArgs();
                        List<Local> params = dest.getActiveBody().getParameterLocals();
                        for (int i = 0; i < invokeExpr.getArgCount(); i++) {
                            Value argument = args.get(i);
                            if (fact.getO1() != null && fact.getO1() == argument) {
                                out.add(new Pair<>(params.get(i), fact.getO2()));
                            } else if (argument instanceof IntConstant) {
                                out.add(new Pair<>(params.get(i), ((IntConstant) argument).value));
                            }
                        }
                        return out;
                    }
                };
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getReturnFlowFunction(Unit callsite, SootMethod callee, Unit exit, Unit retsite) {
                // TODO: Map the return value back into the caller's context if applicable.
                // Since Java has pass-by-value semantics for primitive data types, you do not have to map the formals
                // back to the actuals at the exit of the callee.
                return new FlowFunction<Pair<Local, Integer>>() {
                    @Override
                    public Set<Pair<Local, Integer>> computeTargets(Pair<Local, Integer> fact) {
                        if (exit instanceof ReturnStmt) {
                            ReturnStmt returnStmt = (ReturnStmt) exit;
                            Value returnStmtOp = returnStmt.getOp();

                            if (callsite instanceof AssignStmt) {
                                AssignStmt callsiteAssignStmt = (AssignStmt) callsite;
                                Value callsiteLeftOp = callsiteAssignStmt.getLeftOp();
                                if (callsiteLeftOp instanceof Local) {
                                    Local callsiteLeftLocal = (Local) callsiteLeftOp;
                                    Pair<Local, Integer> newFact = new Pair<>(callsiteLeftLocal, fact.getO2());

                                    if (returnStmtOp instanceof IntConstant) {
                                        int constantValue = ((IntConstant) returnStmtOp).value;
                                        Pair<Local, Integer> newFactC = new Pair<>(callsiteLeftLocal, constantValue);
                                        return Collections.singleton(newFactC);
                                    }
                                    return Collections.singleton(newFact);
                                }
                            }
                        }
                        return Collections.emptySet();
                    }
                };
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getCallToReturnFlowFunction(Unit callsite, Unit retsite) {
                // TODO: getCallToReturnFlowFunction can be left to return id in many analysis; this time as well?
                return new FlowFunction<Pair<Local, Integer>>() {
                    @Override
                    public Set<Pair<Local, Integer>> computeTargets(Pair<Local, Integer> fact) {
                        Set<Pair<Local, Integer>> out = new HashSet<>();
                        out.add(fact);
                        return out;
                    }
                };
            }
        };
    }

    @Override
    protected Pair<Local, Integer> createZeroValue() {
        return new Pair<>(new JimpleLocal("<<zero>>", NullType.v()), Integer.MIN_VALUE);
    }

}
