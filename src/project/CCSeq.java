package src.project;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
    predicate_ctor CCSeq_shared_state(CCSeq cc)() = cc.seq |-> ?cs &*& cs.length |-> ?l &*& cs.capacity |-> ?c &*& c > 0
    &*& cs.sequence |-> ?counters &*& counters.length == c &*& 0 <= l &*& l <= c;
    
    predicate_ctor CCSeq_notfullseq(CCSeq cc)() = cc.seq |-> ?cs &*& cs.length |-> ?l &*& cs.capacity |-> ?c &*& c > 0 &*& l >= 0 &*& l < c;
    
    predicate_ctor CCSeq_notemptyseq(CCSeq cc)() = cc.seq |-> ?cs &*& cs.length |-> ?l &*& cs.capacity |-> ?c &*& c > 0 &*& l > 0 &*& l < c;
    
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
    /*//@ requires cap > 0;
    //@ ensures CCSeqInv(this);*/
    {
        this.seq = new CounterSequence(cap); 
        this.mon = new ReentrantLock();
        //@ close CCSeq_shared_state(this)();
        //@ close set_cond(CCSeq_shared_state(this), CCSeq_notfullseq(this));
        this.notfull = mon.newCondition();
        //@ close set_cond(CCSeq_shared_state(this), CCSeq_notemptyseq(this));
        this.notempty = mon.newCondition();
    }
    
    public int getCounter(int i)
    //@ requires CCSeqInv(this);
    //@ ensures CCSeqInv(this);
    {
        int r = -1;
        if ((0 <= i) && (i<= seq.length())) { //test if i is valid
            mon.lock();
            //@ open CCSeq_shared_state(this);
            r = seq.getCounter(i);
            //@ close CCSeq_shared_state(this);
            mon.unlock();
        }
        return r;
    }
    
    public void incr(int i, int val)
    //@ requires CCSeqInv(this);
    //@ ensures CCSeqInv(this);
    {
        if ((0 <= i) && (i<= seq.length())) { //test if i is valid
            mon.lock();
            //@ open CCSeq_shared_state(this);
            this.seq.increment(i, val);
            //@ close CCSeq_shared_state(this);
            mon.unlock();
        }
    }
    
    public void decr(int i, int val)
    //@ requires CCSeqInv(this);
    //@ ensures CCSeqInv(this);
    {
        if ((0 <= i) && (i<= seq.length())) { //test if i is valid
            this.seq.decrement(i, val);
        }
    }
    
    public int addCounter(int limit)
    //@ requires CCSeqInv(this);
    //@ ensures CCSeqInv(this);
    {
    	int length = 0;
    	mon.lock();
        //@ open CCSeq_shared_state(this);
        this.seq.addCounter(limit);
        length = this.seq.length();
        //@ close CCSeq_shared_state(this);
        mon.unlock();
        return length;
    }
    
    public void remCounter(int i) {
    }
}
