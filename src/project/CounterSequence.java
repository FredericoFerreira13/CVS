package src.project;

/*@
    predicate CounterP(unit a, Counter c; unit b) = CounterInv(c,?v, ?l, ?over) &*& b == unit;
@*/ 


/*@
    predicate CounterSequenceInv(CounterSequence cs; int l, int c) = cs.length |-> l &*& cs.capacity |-> c &*& c > 0
    &*& cs.sequence |-> ?counters &*& counters.length == c &*& 0 <= l &*& l <= c
    &*& array_slice_deep(counters, 0, l, CounterP, unit, _, _) &*& array_slice(counters, l, c, ?counter);
@*/

public class CounterSequence {

    private Counter sequence[];
    private int length;
    private int capacity;
    
    public CounterSequence(int cap)
    //@ requires cap > 0;
    //@ ensures CounterSequenceInv(this, 0, cap);
    {
        this.length = 0;
        this.capacity = cap;
        this.sequence = new Counter[cap];
    }

    public CounterSequence(int[] arr) 
    //@ requires arr != null &*& arr.length > 0 &*& array_slice(arr, 0, arr.length,?vs);
    //@ ensures CounterSequenceInv(this, arr.length, arr.length) &*& array_slice(arr, 0, arr.length,vs);
    {
        this.capacity = arr.length;
        this.length = arr.length;
        this.sequence = new Counter[capacity];

        for(int i = 0; i < arr.length; i++)
        //@ invariant 0 <= i &*& i <= arr.length;
        {
            Counter c = new Counter(0, arr[i]);
            this.sequence[i] = c;
        }

    }
    
    public int length() 
    //@ requires CounterSequenceInv(this, ?l, ?c);
    //@ ensures CounterSequenceInv(this, l, c) &*& result == l;
    {
        return this.length;
    }
    
    public int capacity() 
    //@ requires CounterSequenceInv(this, ?l, ?c);
    //@ ensures CounterSequenceInv(this, l, c) &*& result == c;
    { 
        return this.capacity; 
    }
    
    public int getCounter(int i) 
    //@ requires CounterSequenceInv(this, ?l, ?c);
    //@ ensures CounterSequenceInv(this, l, c);
    { 
        return this.sequence[i].getVal();
    }
    
    public int addCounter(int limit) { return 0; }
    
    public void remCounter(int pos) {  }
    
    public void remCounterPO(int pos) {  }
    
    public void increment(int i, int val) {  }
    
    public void decrement(int i, int val) {  }
}
