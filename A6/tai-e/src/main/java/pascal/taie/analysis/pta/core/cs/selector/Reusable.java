package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.heap.Obj;

// Reusable.java 不提交到 OJ，可将 class Reusable 放在同一个包的要提交的文件中，例如 _1CallSelector.java

abstract class Reusable {
    public static Context getEmptyContext() {
        return ListContext.make();
    }

    public static <T> Context make2Context(Context parent, T current) {
        var parentLength = parent.getLength();
        return parentLength > 0
                ? ListContext.make(parent.getElementAt(parentLength - 1), current)
                : ListContext.make(current);
    }

    public static Context select0HeapContext(CSMethod method, Obj obj) {
        return getEmptyContext();
    }

    public static Context select1HeapContext(CSMethod method, Obj obj) {
        var context = method.getContext();
        var length = context.getLength();
        return length > 0
                ? ListContext.make(context.getElementAt(length - 1))
                : getEmptyContext();
    }
}
