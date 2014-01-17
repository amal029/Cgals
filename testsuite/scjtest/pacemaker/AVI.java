package pacemaker;

import static pacemaker.SCJMain.clk;

import javax.realtime.Clock;
import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.StorageParameters;

public class AVI extends PeriodicEventHandler{
	public SynchronizeHandler port_AP;
	public SynchronizeHandler port_VP;
	public SynchronizeHandler port_AS;
	public SynchronizeHandler port_VS;
	
	private int STATE = 0;
	public Timer time = new Timer();

	public AVI(PriorityParameters priority, PeriodicParameters release,
			StorageParameters storage, long scopeSize) {
		super(priority, release, storage, scopeSize);
		ID = priority.getPriority();
		time.refreshTime();
	}
	
	final int ID;

	@Override
	public void handleAsyncEvent() {
		boolean sAP  = this.port_AP.get_broadcast(ID);
		boolean sAS = port_AS.get_broadcast(ID);
		boolean sVS = port_VS.get_broadcast(ID);
//		System.out.println(""+clk.getTimeinMilliSeconds()+" "+ Timer.TURI);
		switch(STATE){
		case 0:
			if(sAS || sAP){
				if(sAS)
					System.out.println("AVI: GOT AS");
				if(sAP)
					System.out.println("AVI: GOT AP");
				STATE = 1;
				time.refreshTime();
			}
			break;
		case 1:
			long t = time.getTimeinMilliSeconds();
			long cclk = clk.getTimeinMilliSeconds();
			if(sVS){
				System.out.println("AVI: Cycle done");
				STATE = 0;
			}
			else if(t >= Timer.TAVI && cclk >= Timer.TURI){
				port_VP.broadcast();
//				VP = true;
				STATE = 0;
				System.out.println("Emitted VP (1)");
			}
			else if(t >= Timer.TAVI && cclk < Timer.TURI){
				STATE = 2;
			}
			break;
		case 2:
			cclk = clk.getTimeinMilliSeconds();
			if(sVS){
				System.out.println("AVI: cycle done - TAVI >");
				STATE = 0;
			}
			else if(cclk >= Timer.TURI){
				port_VP.broadcast();
//				VP = true;
				STATE = 0;
				System.out.println("AVI: Emitted VP (2)");
			}
			break;
		default: break;
		}
	}

}
