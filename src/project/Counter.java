//verifast_options{disable_overflow_check}

package src.project;

/*@
    predicate CounterInv(Counter c; int v, int l, boolean over) = c.val |-> v &*& c.limit |-> l &*& c.overflow |-> over &*& 0 <= v &*& v < l;
@*/

public class Counter {
    
    private int val;
    private int limit;
    private boolean overflow;

    public Counter(int val, int limit) 
    //@ requires val >= 0 &*& val < limit &*& limit > 0;
    //@ ensures CounterInv(this,val,limit,false);
    {     
        this.val = val;
        this.limit = limit;
        this.overflow = false;
    }

    public int getVal() 
    //@ requires CounterInv(this,?val,?limit,?overflow);
    //@ ensures CounterInv(this,val,limit,overflow) &*& result == val;
    { 
        return this.val;
    }

    public int getLimit() 
    //@ requires CounterInv(this,?val,?limit,?overflow);
    //@ ensures CounterInv(this,val,limit,overflow) &*& result == limit;
    { 
        return this.limit;
    }

    public void incr(int v) 
    //@ requires CounterInv(this,?val,?limit,?overflow) &*& v >= 0;
    //@ ensures ((val + v >= limit) ? CounterInv(this,(val+v) % limit, limit,true) : CounterInv(this,val+v,limit,overflow));
    {  
        if(this.val 
        + v >= this.limit){
            this.val = (this.val + v) % this.limit;
            this.overflow = true;
        }
        else{
            this.val = this.val + v;
        }
    }

    public void decr(int v) 
    //@ requires CounterInv(this,?val,?limit,?overflow) &*& v >= 0;
    //@ ensures ((val - v < 0) ? CounterInv(this,0,limit,true) : CounterInv(this,val-v,limit,overflow));
    {
        if(this.val - v < 0){
            this.val = 0;
            this.overflow = true;
        } 
        else {
            this.val = this.val - v;
        }
    }
}
