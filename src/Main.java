package src;
import src.project.*;

public class Main {

    public void doMain()
        //@ ensures true
        //@ requires true
    {
    int CAP = 10;
    CCSeq seq = new CCSeq(CAP);

    for(int i = 0; i < 100; i++)
    {
        new Thread();
    }
    
}
}
