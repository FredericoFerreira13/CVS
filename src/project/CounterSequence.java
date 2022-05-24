package src.project;

/*@
    predicate CounterP(unit a, Counter c; unit b) = CounterInv(?v, ?l, ?over) &*& b == unit;
@*/ 


/*@
    predicate CounterSequenceInv(CounterSequence cs; int l, int c) = cs.length |-> l &*& cs.capacity |-> c &*& c > 0
    &*& this.sequence |-> ?counters &*& counters.length == c &*& 0 <= l &*& l <= c
    &*& array_slice_deep(counters, 0, l, CounterP, unit, _, _) &*& array_slice(counters, l, c, ?counter);
@*/

public class CounterSequence {

    Counter sequence[];
    int length;
    int capacity;
    
    public CounterSequence(int cap)
    //@ requires cap > 0;
    //@ ensures CounterSequenceInv(this, length, capacity);
    {
        length = 0;
        capacity = cap;
        sequence = new Counter[cap];
    }

    public CounterSequence(int[] arr) {  }
    
    public int length() { return 0; }
    
    public int capacity() { return 0; }
    
    public int getCounter(int i) { return 0; }
    
    public int addCounter(int limit) { return 0; }
    
    public void remCounter(int pos) {  }
    
    public void remCounterPO(int pos) {  }
    
    public void increment(int i, int val) {  }
    
    public void decrement(int i, int val) {  }
}
