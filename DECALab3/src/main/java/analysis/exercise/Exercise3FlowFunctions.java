package analysis.exercise;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import com.google.common.collect.Sets;

import analysis.TaintAnalysisFlowFunctions;
import analysis.VulnerabilityReporter;
import analysis.fact.DataFlowFact;
import heros.FlowFunction;
import soot.Local;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.*;
import soot.jimple.internal.JInstanceFieldRef;

public class Exercise3FlowFunctions extends TaintAnalysisFlowFunctions {

	private VulnerabilityReporter reporter;

	public Exercise3FlowFunctions(VulnerabilityReporter reporter) {
		this.reporter = reporter;
	}

	@Override
	public FlowFunction<DataFlowFact> getCallFlowFunction(Unit callSite, SootMethod callee) {
		return new FlowFunction<DataFlowFact>() {
			@Override
			public Set<DataFlowFact> computeTargets(DataFlowFact fact) {
				if(fact.equals(DataFlowFact.zero()))
					return Collections.emptySet();
				prettyPrint(callSite, fact);
				Set<DataFlowFact> out = Sets.newHashSet();
				if(!(callSite instanceof Stmt)){
					return out;
				}
				Stmt callSiteStmt = (Stmt) callSite;
				//TODO: Implement Exercise 1c) here
				if (callSiteStmt instanceof InvokeStmt && callSiteStmt.containsInvokeExpr()) {
					InvokeStmt invokeStmt = (InvokeStmt) callSiteStmt;
					List<Value> args = invokeStmt.getInvokeExpr().getArgs();
					List<Local> params = callee.getActiveBody().getParameterLocals();
					//TODO: Implement interprocedural part of Exercise 3 here
					for (int i = 0; i < invokeStmt.getInvokeExpr().getArgCount(); i++) {
						Value argument = args.get(i);
						if (fact.getVariable() != null && fact.getVariable() == argument) {
							out.add(new DataFlowFact(params.get(i), fact.getField()));
						}
//						fact.getField().getType().equals(invokeStmt.getInvokeExpr().getArg(0).getType())
					}
				}
				return out;
			}

		};
	}

	public FlowFunction<DataFlowFact> getCallToReturnFlowFunction(final Unit call, Unit returnSite) {
		return new FlowFunction<DataFlowFact>() {

			@Override
			public Set<DataFlowFact> computeTargets(DataFlowFact val) {

				Set<DataFlowFact> out = Sets.newHashSet();
				Stmt callSiteStmt = (Stmt) call;
				out.add(val);
				modelStringOperations(val, out, callSiteStmt);
				
				if(val.equals(DataFlowFact.zero())){
					//TODO: Implement Exercise 1a) here
					if (callSiteStmt instanceof AssignStmt) {
						Value leftOp = ((AssignStmt) callSiteStmt).getLeftOp();
						Value rightOp = ((AssignStmt) callSiteStmt).getRightOp();

						if (leftOp instanceof Local && rightOp.toString().contains("java.lang.String getParameter(java.lang.String)")) {
							out.add(new DataFlowFact((Local) leftOp));
						}
					}
				}
				if(call instanceof Stmt && call.toString().contains("executeQuery")){
					Stmt stmt = (Stmt) call;
					Value arg = stmt.getInvokeExpr().getArg(0);
					if(val.getVariable().equals(arg)){
						reporter.reportVulnerability();
					}
				}
				return out;
			}
		};
	}
	private void modelStringOperations(DataFlowFact fact, Set<DataFlowFact> out,
			Stmt callSiteStmt) {
		if(callSiteStmt instanceof AssignStmt && callSiteStmt.toString().contains("java.lang.StringBuilder append(") && callSiteStmt.getInvokeExpr() instanceof InstanceInvokeExpr){
			Value arg0 = callSiteStmt.getInvokeExpr().getArg(0);
			Value base = ((InstanceInvokeExpr) callSiteStmt.getInvokeExpr()).getBase();
			/*Does the propagated value match the first parameter of the append call or the base variable*/
			if(fact.getVariable().equals(arg0) || fact.getVariable().equals(base)){ 
				/*Yes, then taint the left side of the assignment*/
				Value leftOp = ((AssignStmt) callSiteStmt).getLeftOp();
				if(leftOp instanceof Local){
					out.add(new DataFlowFact((Local) leftOp));
				}
			}
		}
		

		/*For any call x = var.toString(), if the base variable var is tainted, then x is tainted.*/
		if(callSiteStmt instanceof AssignStmt && callSiteStmt.toString().contains("toString()")){
			if(callSiteStmt.getInvokeExpr() instanceof InstanceInvokeExpr){
				InstanceInvokeExpr instanceInvokeExpr = (InstanceInvokeExpr) callSiteStmt.getInvokeExpr();
				if(fact.getVariable().equals(instanceInvokeExpr.getBase())){
					Value leftOp = ((AssignStmt) callSiteStmt).getLeftOp();
					if(leftOp instanceof Local){
						out.add(new DataFlowFact((Local) leftOp));
					}
				}
			}
		}
	}
	private DataFlowFact fieldSensitiveDataFlowFact(Value value) {
		if (value instanceof Local)
			return new DataFlowFact((Local) value);
		if (value instanceof JInstanceFieldRef) {
			JInstanceFieldRef fieldRef = ((JInstanceFieldRef) value);
			return new DataFlowFact((Local) fieldRef.getBase(), fieldRef.getField());
		}
		return null;
	}
	@Override
	public FlowFunction<DataFlowFact> getNormalFlowFunction(final Unit curr, Unit succ) {
		return new FlowFunction<DataFlowFact>() {
			@Override
			public Set<DataFlowFact> computeTargets(DataFlowFact fact) {
				prettyPrint(curr, fact);
				Set<DataFlowFact> out = Sets.newHashSet();
				out.add(fact);

				//TODO: Implement Exercise 1a) here
				if (curr instanceof AssignStmt) {
					Value leftOp = ((AssignStmt) curr).getLeftOp();
					Value rightOp = ((AssignStmt) curr).getRightOp();

					//TODO: Implement cases for field load and field store statement of Exercise 3) here
					DataFlowFact rightDF = fieldSensitiveDataFlowFact(rightOp);
					DataFlowFact leftDF = fieldSensitiveDataFlowFact(leftOp);

					if (rightOp instanceof Constant) {
						if (fact.equals(leftDF)) {
							return Collections.emptySet();
						}
						return out;
					}
					if (rightDF == null)
						return out;

					boolean varPassed = false;
					boolean fieldPassed = false;

					if (fact.getVariable() != null && rightDF.getVariable() != null && fact.getVariable().equals(rightDF.getVariable())) {  // x = y <fact=y>
						varPassed = true;
					}

					if (fact.getField() != null && rightDF.getField() != null && fact.getField().equals(rightDF.getField())) { // x
						fieldPassed = true;
					} else if (fact.getField() == null && rightDF.getField() == null) {
						fieldPassed = true;
					}

					if (varPassed && fieldPassed)
						out.add(leftDF);
				}
				return out;
			}
		};
	}

	@Override
	public FlowFunction<DataFlowFact> getReturnFlowFunction(Unit callSite, SootMethod callee, Unit exitStmt, Unit retSite) {
		return new FlowFunction<DataFlowFact>() {
			@Override
			public Set<DataFlowFact> computeTargets(DataFlowFact fact) {
				prettyPrint(callSite, fact);
				return Collections.emptySet();
			}
		};
	}
	
}
