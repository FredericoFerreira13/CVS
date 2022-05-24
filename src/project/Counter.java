package src.project;

/*@
    predicate CounterInv(int v, int l, boolean over) = this.val |-> v &*& this.limit |-> l &*& this.overflow |-> over &*& 0 <= v &*& v < l;
@*/

public class Counter {
    
    private int val;
    private int limit;
    private boolean overflow;

    public Counter(int val, int limit) 
    //@ requires val >= 0 &*& val < limit &*& limit > 0;
    //@ requires CounterInv(val,limit,false);
    {     
        this.val = val;
        this.limit = limit;
        this.overflow = false;
    }

    public int getVal() 
    //@ requires CounterInv(?val,?limit,?overflow);
    //@ ensures CounterInv(val,limit,overflow) &*& result == val;
    { 
        return this.val;
    }

    public int getLimit() 
    //@ requires CounterInv(?val,?limit,?overflow);
    //@ ensures CounterInv(val,limit,overflow) &*& result == limit;
    { 
        return this.limit;
    }

    public void incr(int v) 
    //@ requires CounterInv(?val,?limit,?overflow) &*& v >= 0;
    //@ ensures (val + v >= limit)? then CounterInv( (val+v) % limit, limit,true) : CounterInv(val+v,limit,overflow)
    {  
        if(val + v >= limit){
            this.val = (this.val + v) % limit;
            this.overflow = true;
        }
        else{
            this.val = this.val + v;
        }
    }

    public void decr(int v) 
    //@ requires CounterInv(?val,?limit,?overflow) &*& v >= 0;
    //@ ensures (val - v < 0)? then CounterInv(0,limit,true) : CounterInv(val-v,limit,overflow)
    {
        if(val - v < 0){
            this.val = 0;
            this.overflow = true;
        } 
        else {
            this.val = this.val - v;
        }
    }
}
