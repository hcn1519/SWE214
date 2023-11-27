package analysis.exercise;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import com.google.common.collect.Sets;

import analysis.TaintAnalysisFlowFunctions;
import analysis.VulnerabilityReporter;
import analysis.fact.DataFlowFact;
import heros.FlowFunction;
import polyglot.ast.Assign;
import polyglot.ext.param.types.Param;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.*;

public class Exercise1FlowFunctions extends TaintAnalysisFlowFunctions {

	private VulnerabilityReporter reporter;

	public Exercise1FlowFunctions(VulnerabilityReporter reporter) {
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

				if(!(callSite instanceof Stmt) || !callee.hasActiveBody())
					return out;

				List<Value> callSiteArgs = ((Stmt) callSite).getInvokeExpr().getArgs();
				List<Local> params = callee.getActiveBody().getParameterLocals();
				Local factLocal = fact.getVariable();
				for (int i = 0; i < callSiteArgs.size(); i++) {
					Value callSiteArg = callSiteArgs.get(i);
					if (factLocal.equivTo(callSiteArg)) {
						out.add(dataFlowfact(params.get(i)));
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
				prettyPrint(call, val);
				Set<DataFlowFact> out = Sets.newHashSet();
				Stmt callSiteStmt = (Stmt) call;
				out.add(val);
				modelStringOperations(val, out, callSiteStmt);

				if (val.equals(DataFlowFact.zero())) {
					if (callSiteStmt instanceof AssignStmt) {
						Value lhs = ((AssignStmt) callSiteStmt).getLeftOp();
						out.add(dataFlowfact(lhs));
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

	private DataFlowFact dataFlowfact(Value value) {
		if (value instanceof Local)
			return new DataFlowFact((Local)value);

		if (value instanceof InstanceFieldRef) {
			Local local = (Local) ((InstanceFieldRef) value).getBase();
			return new DataFlowFact(local);
		}
		return null;
	}

	@Override
	public FlowFunction<DataFlowFact> getNormalFlowFunction(final Unit curr, Unit succ) {
		return new FlowFunction<DataFlowFact>() {
			@Override
			public Set<DataFlowFact> computeTargets(DataFlowFact fact) {
				prettyPrint(curr, fact);
				if (!(curr instanceof AssignStmt))
					return Collections.singleton(fact);

				AssignStmt assignStmt = (AssignStmt) curr;
				Value lhs = assignStmt.getLeftOp();
				Value rhs = assignStmt.getRightOp();

				// kill lhs if rhs is Constant
				if (rhs instanceof Constant) {
					// kill, i.e. y = 0, <fact = y>
					if (lhs.equivTo(fact.getVariable())) {
						return Collections.emptySet();
					}
					// keep, i.e. y = 0, <fact = ZERO>
					return Collections.singleton(fact);
				}

				// keep prev fact if rhs is not related to fact
				// i.e. stmt: x = y; <fact = this>
				if (!rhs.equivTo(fact.getVariable())) {
					return Collections.singleton(fact);
				}

				// gen lhs dataflow fact
				Set<DataFlowFact> out = Sets.newHashSet();
				out.add(fact);
				DataFlowFact lhsDataFlowFact = dataFlowfact(lhs);
				out.add(lhsDataFlowFact);
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
