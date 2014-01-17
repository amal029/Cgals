package pacemaker;

import static pacemaker.SCJMain.clk;

import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.StorageParameters;

public class LRI extends PeriodicEventHandler{
	public SynchronizeHandler port_AP;
	public SynchronizeHandler port_VP;
	public SynchronizeHandler port_AS;
	public SynchronizeHandler port_VS;
	private int STATE = 0;
	
	public Timer time = new Timer();
	
	public LRI(PriorityParameters priority, PeriodicParameters release,
			StorageParameters storage, long scopeSize) {
		super(priority, release, storage, scopeSize);
		ID = priority.getPriority();
		time.refreshTime();
	}

	final int ID;
	@Override
	public void handleAsyncEvent() {
		boolean sVP = (this.port_VP.get_broadcast(ID));
		boolean sAS = port_AS.get_broadcast(ID);
		boolean sVS = port_VS.get_broadcast(ID);
		
		switch(STATE){
		case 0:
			if(time.getTimeinMilliSeconds() >= Timer.TLRI-Timer.TAVI){
				port_AP.broadcast();
//				AP = true;
				STATE = 0;
				System.out.println("LRI: TIME_OUT - Emitted AP");
				time.refreshTime();
			}
			if(sAS){
				System.out.println("LRI: GOT AS");
				STATE = 1; 
			}
			if(sVP || sVS){
				if(sVS)
					System.out.println("LRI: Got VS");
				if(sVP)
					System.out.println("LRI: GOT VP");
				time.refreshTime();
			}
			break;
		case 1:
			if(sVP || sVS){
				if(sVS)
					System.out.println("LRI: Got VS");
				if(sVP)
					System.out.println("LRI: GOT VP");
				System.out.println("LRI: cycle done");
				STATE = 0;
				time.refreshTime();
			}
			break;
		default: break;
		}

	}

}
