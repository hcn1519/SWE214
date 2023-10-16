package analysis.exercise1;

import analysis.AbstractAnalysis;
import analysis.VulnerabilityReporter;
import soot.Body;
import soot.RefType;
import soot.Unit;
import soot.ValueBox;
import soot.jimple.internal.JAssignStmt;

public class MisuseAnalysis extends AbstractAnalysis{
	public MisuseAnalysis(Body body, VulnerabilityReporter reporter) {
		super(body, reporter);
	}
	
	@Override
	protected void flowThrough(Unit unit) {
		Class<? extends Unit> unitClass = unit.getClass();
		if (!unitClass.equals(soot.jimple.internal.JAssignStmt.class)) {
			return;
		}
		if (!((JAssignStmt) unit).containsInvokeExpr()) {
			return;
		}
		soot.Value rightOp = ((JAssignStmt) unit).getRightOp();
		if (!this.isCipherRefType(rightOp)) {
			return;
		}

		for (ValueBox valueBox : rightOp.getUseBoxes()) {
			if (this.isVulnerableCipherString(valueBox.getValue().toString())) {
				reporter.reportVulnerability("<target.exercise1.Misuse: void test()>", unit);
			}
		}
	}

	private boolean isCipherRefType(soot.Value rightOp) {
		return rightOp.getType() instanceof RefType
				&& ((RefType) rightOp.getType()).getClassName().equals("javax.crypto.Cipher");
	}

	private boolean isVulnerableCipherString(String value) {
		return !value.contains("/");
	}
}