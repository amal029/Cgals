package pacemaker;

import javax.realtime.Clock;

public class Timer {
	public final static int TLRI = 5000;
	public final static int TAVI = 1000;
	public final static int TURI = 2000;
	
	public long TIME = Clock.getRealtimeClock().getTime().getMilliseconds();
	
	public void refreshTime(){ TIME = Clock.getRealtimeClock().getTime().getMilliseconds(); }
	public long getTimeinMilliSeconds(){
		return Clock.getRealtimeClock().getTime().getMilliseconds() - TIME;
	}
}
