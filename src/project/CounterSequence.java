package src.project;

/*@
    predicate CounterP(unit a, Counter c; unit b) = CounterInv(c,?v, ?l, ?over) &*& b == unit;
@*/ 


/*@
    predicate Positive(unit a, int v; unit n) = v > 0 &*& n == unit;
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
    //@ requires arr != null &*& arr.length > 0 &*& array_slice_deep(arr, 0, arr.length, Positive, unit, ?vs, _);
    //@ ensures CounterSequenceInv(this, arr.length, arr.length);
    {
        this.capacity = arr.length;
        this.length = arr.length;
        this.sequence = new Counter[capacity];

        for(int i = 0; i < arr.length; i++)
        /*@ 
            invariant 0 <= i &*& i <= arr.length 
            &*& array_slice_deep(arr, 0, arr.length, Positive, unit, _, _)
            &*& this.sequence |-> ?counters 
            &*& counters.length == arr.length
            &*& array_slice(counters,i,arr.length,?v) 
            &*& array_slice_deep(counters,0,i,CounterP,unit, _,_);
        @*/
        {
            this.sequence[i] = new Counter(0, arr[i]);
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
    // requires CounterSequenceInv(this, ?l, ?c) &*& i>=0 &*& i < l;
    // ensures CounterSequenceInv(this, l, c) &*& CounterInv(_,result,_,_);
    { 
        return this.sequence[i].getVal();
    }
    
    public int addCounter(int limit) 
    //@ requires CounterSequenceInv(this, ?l, ?c) &*& limit > 0 &*& l<c;
    //@ ensures CounterSequenceInv(this, l+1, c) &*& result == l;
    { 
        Counter d = new Counter(0, limit);
        this.sequence[this.length] = d;
        //@ array_slice_deep_close(sequence,l,CounterP,unit);
        this.length = this.length+1;
        return this.length-1;
    }
    
    public void remCounter(int pos) 
    // requires CounterSequenceInv(this, ?l, ?c) &*& pos >= 0 &*& pos < l &*& l > 0;
    // ensures CounterSequenceInv(this, l-1 ,c);
    {  
        this.sequence[pos] = this.sequence[length-1];
        this.sequence[length-1] = null;
        this.length = this.length - 1;
    }
    
    public void remCounterPO(int pos) 
    // requires CounterSequenceInv(this, ?l, ?c) &*& pos >= 0 &*& pos < l &*& l > 0;
    // ensures CounterSequenceInv(this, l-1 ,c);
    {
        for(int i = pos; i < this.length-1; i++)
        /*@ invariant this.length |-> l 
            &*& pos <= i &*& i <= l - 1
            &*& this.sequence |-> ?counters 
            &*& counters.length == c
            &*& array_slice_deep(counters,i,l-1,CounterP,unit, _,_);
        @*/
        {
            this.sequence[i] = this.sequence[i+1];
        }
        this.sequence[this.length-1] = null;
        this.length = this.length - 1;
    }
    
    public void increment(int i, int val) 
    //@ requires CounterSequenceInv(this, ?l, ?c) &*& i >= 0 &*& i < l &*& val >= 0;
    //@ ensures CounterSequenceInv(this, l ,c);
    {  
        this.sequence[i].incr(val);
    }
    
    public void decrement(int i, int val) 
    //@ requires CounterSequenceInv(this, ?l, ?c) &*& i >= 0 &*& i < l &*& val >= 0;
    //@ ensures CounterSequenceInv(this, l ,c);
    {
        this.sequence[i].decr(val);
    }
}
