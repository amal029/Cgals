package pacemaker;

import static pacemaker.IO.VP;

import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.StorageParameters;

public class URI extends PeriodicEventHandler{
	public SynchronizeHandler port_VP;
	public SynchronizeHandler port_VS;
	
	public URI(PriorityParameters priority, PeriodicParameters release,
			StorageParameters storage, long scopeSize) {
		super(priority, release, storage, scopeSize);
		ID = priority.getPriority();
	}

	final int ID;
	@Override
	public void handleAsyncEvent() {
		boolean sVP = port_VP.get_broadcast(ID);
		boolean sVS = port_VS.get_broadcast(ID);
		
		if(sVP || sVS){
			SCJMain.clk.refreshTime();
		}
	}

}
