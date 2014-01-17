package pacemaker;

import javax.realtime.PeriodicParameters;
import javax.realtime.PriorityParameters;
import javax.safetycritical.PeriodicEventHandler;
import javax.safetycritical.StorageParameters;


public class EnvironmentInterface extends PeriodicEventHandler{
	public SynchronizeHandler port_AS;
	public SynchronizeHandler port_VS;
	public Timer time = new Timer();
	public EnvironmentInterface(PriorityParameters priority, PeriodicParameters release,
			StorageParameters storage, long scopeSize) {
		super(priority, release, storage, scopeSize);
		ID = priority.getPriority();
		time.refreshTime();
	}

	final int ID;
	int STATE = 0;
	@Override
	public void handleAsyncEvent() {
		
		if(time.getTimeinMilliSeconds() > 100){
			port_AS.broadcast();
		}
		if(time.getTimeinMilliSeconds() > 400){
			port_VS.broadcast();
			time.refreshTime();
		}
		
	}

}
