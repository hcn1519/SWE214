package target.exercise3;

import target.exercise2.FifthLeafClass;
import target.exercise2.LeafClass;
import target.exercise2.SixthLeafClass;
import target.exercise2.SomeInterface;

public class SimpleScenario2 {
    private static SomeInterface staticField;

    public static void main(String[] args) {
        SomeInterface leaf = new LeafClass();
        SomeInterface fourthLeaf = getFifthLeafClassIndirectly1();

        LeafClass aliasLeaf = (LeafClass)leaf;

        leaf.doSomething();
        fourthLeaf.doSomething();
        aliasLeaf.doSomething();

        staticField = new SixthLeafClass();

        SomeInterface newStuff = staticField;

        newStuff.doSomething();
    }
    private static SomeInterface getFifthLeafClassIndirectly1() {
        return getFifthLeafClassIndirectly2();
    }
    private static SomeInterface getFifthLeafClassIndirectly2() {
        return getFifthLeafClass();
    }
    private static SomeInterface getFifthLeafClass() {
        return new FifthLeafClass();
    }
}