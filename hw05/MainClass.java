import com.oocourse.elevator1.TimableOutput;

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
        for (int i = 1; i <= 6; i++) {
            RequestQueue eleRequest = new RequestQueue();
            subRequestQueues.add(eleRequest);
            Thread elevator = new Elevator(i, eleRequest);
            elevator.start();
        }

        Thread inputThread = new InputThread(mainRequest);
        inputThread.start();

        Thread schedule = new Schedule(mainRequest, subRequestQueues);
        schedule.start();
    }
}