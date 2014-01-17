package pacemaker;
import javax.realtime.*;
import javax.safetycritical.*;

import washing.*;

public class SCJMain extends CyclicExecutive implements Safelet<CyclicExecutive>{
	private static final long PERIOD = 10;
	private static final long DURATION = 250;
	private static final long MISSION_MEMORY_SIZE = 1000000;
	private static final long IMMORTAL_MEMORY_SIZE = 1000000;
	public static Timer clk = new Timer();

	// Mission implementations - goes to Mission memory
	@Override
		protected void initialize() {
			SynchronizeHandler intf = new SynchronizeHandler(4);
			SynchronizeHandler intf2 = new SynchronizeHandler(4);
			SynchronizeHandler AS_intf = new SynchronizeHandler(4);
			SynchronizeHandler VS_intf = new SynchronizeHandler(4);
			clk.refreshTime();
			
			int i = 0;
			URI task0 = new URI(
					new PriorityParameters(i++),
					new PeriodicParameters(null, new RelativeTime(50, 0)),
					new StorageParameters(50000,null),
					20000 /* INSERT_SCOPE_SIZE_HERE */);
			task0.register();
			task0.port_VP = intf2;
			task0.port_VS = VS_intf;
			
			LRI task1 = new LRI(
					new PriorityParameters(i++),
					new PeriodicParameters(null, new RelativeTime(50, 0)),
					new StorageParameters(50000,null),
					20000 /* INSERT_SCOPE_SIZE_HERE */);
			task1.port_AP = intf;
			task1.port_VP = intf2;
			task1.port_AS = AS_intf;
			task1.port_VS = VS_intf;
			task1.register();
			
			AVI task2 = new AVI(
					new PriorityParameters(i++),
					new PeriodicParameters(null, new RelativeTime(50, 0)),
					new StorageParameters(50000,null),
					20000 /* INSERT_SCOPE_SIZE_HERE */);
			task2.port_AP = intf;
			task2.port_VP = intf2;
			task2.port_AS = AS_intf;
			task2.port_VS = VS_intf;
			task2.register();

			
			EnvironmentInterface task3 = new EnvironmentInterface(
					new PriorityParameters(i++),
					new PeriodicParameters(null, new RelativeTime(50, 0)),
					new StorageParameters(50000,null),
					20000 /* INSERT_SCOPE_SIZE_HERE */);
			task3.port_AS = AS_intf;
			task3.port_VS = VS_intf;
			task3.register();
			

		}
	@Override
		public long missionMemorySize() {return MISSION_MEMORY_SIZE;}
	@Override
		public CyclicSchedule getSchedule(PeriodicEventHandler[] handlers) {
			Frame[] frames = new Frame[1];
			frames[0] = new Frame(new RelativeTime(DURATION, 0), handlers);
			return new CyclicSchedule(frames);
		}

	// Safelet implementations - goes to Immortal memory
	@Override
		public void initializeApplication() {}
	@Override
		public MissionSequencer<CyclicExecutive> getSequencer() {
			StorageParameters sp = new StorageParameters(1000000,null);
			return new LinearMissionSequencer<CyclicExecutive>(new PriorityParameters(0),
					sp,false,this);
		}
	@Override
		public long immortalMemorySize() {
			return IMMORTAL_MEMORY_SIZE;
		}
	public static void main (String[] args) {
		Safelet<CyclicExecutive> m = new SCJMain();
		JopSystem js = new JopSystem();
		js.startCycle(m);
	}
}
