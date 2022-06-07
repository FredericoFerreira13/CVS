package src.project;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
    predicate_ctor CCSeq_shared_state(CCSeq cc)() = cc.seq |-> ?cs &*& cs.length |-> ?l &*& cs.capacity |-> ?c &*& c > 0
    &*& cs.sequence |-> ?counters &*& counters.length == c &*& 0 <= l &*& l <= c
    &*& array_slice_deep(counters, 0, l, CounterP, unit, _, _) &*& array_slice(counters, l, c, ?counter);
    
    predicate_ctor CCSeq_notfullseq(CCSeq cc)() = cc.seq |-> ?cs &*& cs.length |-> ?l &*& cs.capacity |-> ?c &*& c > 0 &*& l >= 0 &*&
    l < c &*& cs.sequence |-> ?counters &*& counters.length == c &*& array_slice_deep(counters, 0, l, CounterP, unit, _, _)
    &*& array_slice(counters, l, c, ?counter);
    
    predicate_ctor CCSeq_notemptyseq(CCSeq cc)() = cc.seq |-> ?cs &*& cs.length |-> ?l &*& cs.capacity |-> ?c &*& c > 0 &*& l > 0
    &*& l <= c &*& cs.sequence |-> ?counters &*& counters.length == c &*& array_slice_deep(counters, 0, l, CounterP, unit, _, _)
    &*& array_slice(counters, l, c, ?counter);
    
    predicate CCSeqInv(CCSeq cc) = cc.mon |-> ?l &*& l != null &*& lck(l, 1, CCSeq_shared_state(cc))
    &*& cc.notfull |-> ?f &*& f != null &*& cond(f, CCSeq_shared_state(cc), CCSeq_notfullseq(cc))
    &*& cc.notempty |-> ?e &*& e != null &*& cond(e, CCSeq_shared_state(cc), CCSeq_notemptyseq(cc));
@*/

public class CCSeq {
    CounterSequence seq;
    ReentrantLock mon;
    Condition notfull;
    Condition notempty;
    
    public CCSeq(int cap)
    //@ requires cap > 0;
    //@ ensures CCSeqInv(this);
    {
    	this.seq = new CounterSequence(cap);
    	//@ close CCSeq_shared_state(this)();
 	//@ close enter_lck(1, CCSeq_shared_state(this)); 
        this.mon = new ReentrantLock();
        //@ close set_cond(CCSeq_shared_state(this), CCSeq_notfullseq(this));
        this.notfull = mon.newCondition();
        //@ close set_cond(CCSeq_shared_state(this), CCSeq_notemptyseq(this));
        this.notempty = mon.newCondition();
        //@close CCSeqInv(this);
    }
    
    public int getCounter(int i)
    //@ requires CCSeqInv(this);
    //@ ensures CCSeqInv(this);
    {
    	//@ open CCSeqInv(this);
        int r = -1;
        mon.lock();
        //@ open CCSeq_shared_state(this)();
        if ((0 <= i) && (i<seq.length())) { //test if i is valid
            r = seq.getCounter(i);
        }
        //@ close CCSeq_shared_state(this)();
        mon.unlock();
        //@ close CCSeqInv(this);
        return r;
    }
    
    public void incr(int i, int val)
    //@ requires CCSeqInv(this) &*& val>=0;
    //@ ensures CCSeqInv(this);
    {
    	//@ open CCSeqInv(this);
    	mon.lock();
    	//@ open CCSeq_shared_state(this)();
        if ((0 <= i) && (i< seq.length())) { //test if i is valid
            this.seq.increment(i, val);
        }
        //@ close CCSeq_shared_state(this)();
        mon.unlock();
        //@ close CCSeqInv(this);
    }
    
    public void decr(int i, int val)
    //@ requires CCSeqInv(this) &*& val>=0;
    //@ ensures CCSeqInv(this);
    {
    	//@ open CCSeqInv(this);
    	mon.lock();
    	//@ open CCSeq_shared_state(this)();
        if ((0 <= i) && (i< seq.length())) { //test if i is valid
            this.seq.decrement(i, val);
        }
        //@ close CCSeq_shared_state(this)();
        mon.unlock();
        //@ close CCSeqInv(this);
    }
    
    public int addCounter(int limit)
    //@ requires CCSeqInv(this) &*& limit > 0;
    //@ ensures CCSeqInv(this);
    {
    	int length = 0;
    	//@ open CCSeqInv(this);
    	
    	mon.lock();
    	//@ open CCSeq_shared_state(this)();
    	
    	while(seq.length() == seq.capacity())
    	/*@ invariant this.seq |-> ?cs &*& cs.length |-> ?l &*& cs.capacity |-> ?c &*& c > 0
    	&*& cs.sequence |-> ?counters &*& counters.length == c &*& 0 <= l &*& l <= c
    	&*& this.notfull |-> ?f &*& f != null &*& cond(f, CCSeq_shared_state(this), CCSeq_notfullseq(this))
    	&*& this.notempty |-> ?e &*& e != null &*& cond(e, CCSeq_shared_state(this), CCSeq_notemptyseq(this))
    	&*& array_slice_deep(counters, 0, l, CounterP, unit, _, _) &*& array_slice(counters, l, c, ?counter);
    	@*/
    	{
    		//@ close CCSeq_shared_state(this)();
    		try { notfull.await(); } catch (InterruptedException exc) {}
    		//@ open CCSeq_notfullseq(this)();
        }
        this.seq.addCounter(limit);
        length = this.seq.length();
        //@ close CCSeq_notemptyseq(this)();
        
        notempty.signal();

        mon.unlock();
        
        //@ close CCSeqInv(this);
        return length;
    }
    
    public void remCounter(int i)
    //@ requires CCSeqInv(this) &*& this.seq |-> ?s &*& s.length |-> ?l &*& i<l;
    //@ ensures CCSeqInv(this);
    
    {
    	int length = 0;
    	//@ open CCSeqInv(this);
	mon.lock();
	//@ open CCSeq_shared_state(this)();
	
    	if ((0 <= i) && (i< seq.length())) { //test if i is valid
	    	
	    	while(seq.length() == seq.capacity())
	    	/*@ invariant this.seq |-> ?cs &*& cs.length |-> ?l &*& cs.capacity |-> ?c &*& c > 0
	    	&*& cs.sequence |-> ?counters &*& counters.length == c &*& 0 <= l &*& l <= c
	    	&*& this.notfull |-> ?f &*& f != null &*& cond(f, CCSeq_shared_state(this), CCSeq_notfullseq(this))
	    	&*& this.notempty |-> ?e &*& e != null &*& cond(e, CCSeq_shared_state(this), CCSeq_notemptyseq(this))
	    	&*& array_slice_deep(counters, 0, l, CounterP, unit, _, _) &*& array_slice(counters, l, c, ?counter);
	    	@*/
	    	{
	    		//@ close CCSeq_shared_state(this)();
	    		try { notempty.await(); } catch (InterruptedException exc) {}
	    		//@ open CCSeq_notemptyseq(this)();
		}
		this.seq.remCounter(i);
		length = this.seq.length();
		//@ close CCSeq_notfullseq(this)();
		
		notfull.signal();  
        }
        mon.unlock();
	//@ close CCSeqInv(this); 
	
        return length;
    }
}
