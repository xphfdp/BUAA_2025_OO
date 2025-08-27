import java.util.ArrayList;
import java.util.Comparator;

import com.oocourse.elevator3.ScheRequest;
import com.oocourse.elevator3.TimableOutput;

public class Schedule extends Thread {

    private static final Object ELEVATOR_CONDITION = new Object();
    private static RequestQueue mainRequestQueue;
    private ArrayList<RequestQueue> subRequestQueues;
    private ArrayList<Elevator> elevators;

    public Schedule() {
        this.mainRequestQueue = new RequestQueue();
        this.subRequestQueues = new ArrayList<>();
        this.elevators = new ArrayList<>();
        for (int i = 0; i < 6; i++) {
            RequestQueue eleRequest = new RequestQueue();
            subRequestQueues.add(eleRequest);
            Elevator elevator = new Elevator(i + 1, eleRequest);
            elevators.add(elevator);
            elevator.start();
        }
    }

    public static Object getElevatorCondition() {
        return ELEVATOR_CONDITION;
    }

    public boolean isFinished() {
        for (RequestQueue requestQueue : subRequestQueues) {
            if (!requestQueue.isAllFinished()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public void run() {
        while (true) {
            if (mainRequestQueue.isEmpty() && mainRequestQueue.isEnd() &&
                    mainRequestQueue.isScheEmpty() && mainRequestQueue.isUpdateEmpty()) {
                if (isFinished()) {
                    for (RequestQueue requestTable : subRequestQueues) {
                        requestTable.setEnd(true);
                    }
                    return;
                } else {
                    try {
                        sleep(Constants.T_REST);
                    } catch (InterruptedException e) {
                        e.printStackTrace();
                    }
                }
            }
            ScheRequest scheRequest = mainRequestQueue.getOneScheRequest();
            if (scheRequest != null) {
                scheElevator(scheRequest);
            }

            Update updateRequest = mainRequestQueue.getOneUpdateRequest();
            if (updateRequest != null) {
                updateElevator(updateRequest);
            }

            Person person = mainRequestQueue.getOneRequest();
            if (person != null) {
                while (true) {
                    int eleId = -1;
                    try {
                        eleId = findBestElevator(person).getEleId();
                    } catch (InterruptedException e) {
                        throw new RuntimeException(e);
                    }
                    if (eleId != -1) {
                        TimableOutput.println("RECEIVE-" + person.getId() + "-" + eleId);
                        subRequestQueues.get(eleId - 1).addRequest(person);
                        break;
                    }
                    try {
                        sleep(1000);
                    } catch (InterruptedException e) {
                        e.printStackTrace();
                    }
                }
            }
        }
    }

    public synchronized void scheElevator(ScheRequest scheRequest) {
        int id = scheRequest.getElevatorId();
        synchronized (subRequestQueues) {
            RequestQueue eleRequest = subRequestQueues.get(id - 1);
            eleRequest.setScheRequest(scheRequest);
        }
    }

    public synchronized void updateElevator(Update updateRequest) {
        int elevatorAId = updateRequest.getElevatorAId();
        int elevatorBId = updateRequest.getElevatorBId();
        synchronized (subRequestQueues) {
            RequestQueue eleRequestA = subRequestQueues.get(elevatorAId - 1);
            RequestQueue eleRequestB = subRequestQueues.get(elevatorBId - 1);
            eleRequestA.setUpdateRequest(updateRequest);
            eleRequestB.setUpdateRequest(updateRequest);
        }
    }

    // 电梯调度核心方法：寻找最合适的电梯
    private Elevator findBestElevator(Person person) throws InterruptedException {
        while (true) {
            Elevator availableEleator = elevators.stream()
                    .filter(e -> !e.isNowInSche() && !e.isFull() && !e.isNowInUpdate()
                            && !e.isDoubleMode())
                    .min(Comparator.comparingInt(Elevator::getElePersonNum)
                            .thenComparingInt(e -> Math.abs(e.getEleFloor() -
                                    person.getFromFloor())))
                    .orElse(null);

            if (availableEleator != null) {
                return availableEleator;
            }

            // 如果所有电梯都处于临时调度，寻找最近的不满电梯
            synchronized (Schedule.getElevatorCondition()) {
                if (elevators.stream().allMatch(Elevator::isNowInSche)) { // 所有电梯都在临时调度
                    Schedule.getElevatorCondition().wait(); // 等待通知
                } else {
                    continue; // 重新检查，可能有电梯刚刚恢复
                }
            }
        }
    }

    public static RequestQueue getMainRequestTable() {
        return mainRequestQueue;
    }
}
