import com.oocourse.elevator2.TimableOutput;

import java.util.ArrayList;

/*
 * 主类
 * 初始化请求队列mainRequest和六个电梯的请求队列verticalRequestTables，
 */

public class MainClass {
    public static void main(String[] args) {
        TimableOutput.initStartTimestamp();
        RequestQueue mainRequest = new RequestQueue();
        ArrayList<RequestQueue> subRequestQueues = new ArrayList<>();
        ArrayList<Elevator> elevators = new ArrayList<>();
        for (int i = 0; i < 6; i++) {
            RequestQueue eleRequest = new RequestQueue();
            subRequestQueues.add(eleRequest);
            Elevator elevator = new Elevator(i + 1, eleRequest);
            elevators.add(elevator);
            elevator.start();
        }
        InputThread inputThread = new InputThread(mainRequest);
        inputThread.start();

        Schedule schedule = new Schedule(mainRequest, subRequestQueues, elevators);
        schedule.start();
    }
}