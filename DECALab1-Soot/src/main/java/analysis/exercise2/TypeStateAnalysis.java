package analysis.exercise2;

import java.util.*;
import analysis.FileState;
import analysis.FileStateFact;
import analysis.ForwardAnalysis;
import analysis.VulnerabilityReporter;
import soot.Body;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;

public class TypeStateAnalysis extends ForwardAnalysis<Set<FileStateFact>> {

	public TypeStateAnalysis(Body body, VulnerabilityReporter reporter) {
		super(body, reporter);
	}

	@Override
	protected void flowThrough(Set<FileStateFact> in, Unit unit, Set<FileStateFact> out) {
		copy(in, out);

		if (unit instanceof soot.jimple.internal.JAssignStmt) {
			JAssignStmt assignStmt = (JAssignStmt) unit;
			Value lhs = assignStmt.getLeftOp();
			Value rhs = assignStmt.getRightOp();
			this.removeKeyIfExist(out, lhs);
			this.addKey(out, rhs, lhs);
		} else if (unit instanceof soot.jimple.internal.JInvokeStmt) {
			JInvokeStmt invokeStmt = (JInvokeStmt) unit;
			InvokeExpr invokeExpr = invokeStmt.getInvokeExpr();
			List<ValueBox> boxes = invokeStmt.getUseBoxes();

			if (!this.method.getSignature().contains("target.exercise2.File") || (long) boxes.size() < 2)
				return;

			Value lhs = boxes.get(0).getValue();
			FileState toState = this.fileStateOfInvokeExpr(invokeExpr);

			if (toState != null)
				this.updateFact(out, toState, lhs);
		} else if (unit instanceof soot.jimple.internal.JReturnVoidStmt && this.hasUnClosedFile(out)) {
			reporter.reportVulnerability(this.method.getSignature(), unit);
		}
		prettyPrint(in, unit, out);
	}

	private boolean hasUnClosedFile(Set<FileStateFact> out) {
		for (FileStateFact fact : out) {
			if (fact.getState() == FileState.Open)
				return true;
		}
		return false;
	}

	private void addKey(Set<FileStateFact> res, Value existingKey, Value newKey) {
		for (FileStateFact fact : res) {
			if (fact.containsAlias(existingKey)) {
				fact.addAlias(newKey);
				break;
			}
		}
	}

	private void removeKeyIfExist(Set<FileStateFact> res, Value key) {
		for (FileStateFact fact : res) {
			if (fact.containsAlias(key)) {
				if (fact.numberOfAlias() == 1)
					res.remove(fact);
				else
					fact.removeAlias(key);
			}
		}
	}

	private FileState stateOfKey(Set<FileStateFact> res, Value key) {
		for (FileStateFact fact : res) {
			if (fact.containsAlias(key))
				return fact.getState();
		}
		return null;
	}

	private void updateFact(Set<FileStateFact> res, FileState toState, Value key) {
		if (toState == FileState.Init) {
			this.removeKeyIfExist(res, key);
			FileStateFact newFact = new FileStateFact(new HashSet<>(Collections.singleton(key)), toState);
			res.add(newFact);
			return;
		}

		FileState currentState = stateOfKey(res, key);
		if (currentState != null) {
			for (FileStateFact fact : res) {
				if (fact.containsAlias(key)) {
					fact.updateState(toState);
				}
			}
		}
	}

	private FileState fileStateOfInvokeExpr(InvokeExpr invokeExpr) {
		if (!invokeExpr.getMethod().getSignature().contains("target.exercise2.File"))
			return null;

		soot.SootMethod method = invokeExpr.getMethod();
		if (method.getName().equals("<init>")) {
			return FileState.Init;
		}  else if (method.getName().equals("open")) {
			return FileState.Open;
		} else if (method.getName().equals("close")) {
			return FileState.Close;
		}
		return null;
	}

	@Override
	protected Set<FileStateFact> newInitialFlow() {
		return new HashSet<>();
	}

	@Override
	protected void copy(Set<FileStateFact> source, Set<FileStateFact> dest) {
		dest.clear();
		for (FileStateFact fact : source) {
			FileStateFact copied = fact.copy();
			dest.add(copied);
		}
	}

	@Override
	protected void merge(Set<FileStateFact> in1, Set<FileStateFact> in2, Set<FileStateFact> out) {
		out.addAll(in1);
		out.addAll(in2);
	}

}
