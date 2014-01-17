package pacemaker;

public class SynchronizeHandler {
	boolean port1_o = false;
	boolean port1_in = false;
	public synchronized boolean sync_o(){
		if(port1_in == true){
			port1_o = false;
			port1_in = false;
			return true;
		}
		else {
			port1_o = true;
			return false;
		}
	}
	public synchronized boolean sync_i(){
		if(port1_o == true && port1_in == false){
			port1_in = true;
			return true;
		}
		else {
			return false;
		}
	}
	
	boolean[] status;
	public SynchronizeHandler(int i){ status = new boolean[i]; }
	public synchronized void broadcast(){
		for(int i=0; i < status.length; i++)
			status[i] = true;
	}
	public synchronized boolean get_broadcast(int i){
		boolean r = status[i];
		status[i] = false;
		return r;
	}
	
}
