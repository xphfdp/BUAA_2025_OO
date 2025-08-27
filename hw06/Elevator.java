import com.oocourse.elevator2.TimableOutput;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class Elevator extends Thread {
    private int id;
    private int elePersonNum;
    private int eleFloor;
    private int direction;
    private int speed;
    private boolean nowInSche; // 是否处于临时调度中
    private RequestQueue eleRequest;
    private Strategy strategy;
    private static HashMap<Object, Object> floorMap = new HashMap<>(); //楼层映射表
    private static int floorNum = 11;
    private HashMap<Integer, ArrayList<Person>> eleMap; // key是目标楼层，value是要到达该楼层的乘客列表
    private List<Person> elePersons;

    public Elevator(int id, RequestQueue eleRequest) {
        this.id = id;
        this.elePersonNum = Constants.ORIGIN_PERSON_NUM;
        this.eleFloor = Constants.ORIGIN_FLOOR_NUM;
        this.direction = 1;
        this.nowInSche = false;
        this.speed = Constants.SPEED;
        this.eleMap = new HashMap<>();
        this.elePersons = new ArrayList<>();
        this.strategy = new Strategy(eleRequest);
        this.eleRequest = eleRequest;
        addMap();
    }

    @Override
    public void run() {
        while (true) {
            if (eleRequest.getScheRequest() != null && !nowInSche) {
                sche();
                continue;
            }
            Advice advice = strategy.getAdvice(eleFloor,
                    elePersonNum, direction, eleMap, nowInSche);
            if (advice == Advice.OVER) {
                break;
            }
            switch (advice) {
                case MOVE:
                    move();
                    break;
                case REVERSE:
                    reverse();
                    break;
                case WAIT:
                    synchronized (eleRequest) {
                        try {
                            eleRequest.wait();
                        } catch (InterruptedException e) {
                            e.printStackTrace();
                        }
                    }
                    break;
                case OPEN:
                    openAndClose();
                    break;
                default:
                    break;
            }
        }
    }

    public void sche() {
        setNowInSche(true);
        if (elePersonNum != 0) {
            personTemOutEle();
        }
        elePersonNum = 0;
        TimableOutput.println("SCHE-BEGIN-" + id);
        Schedule.getMainRequestTable().backToMainRequest(eleRequest);
        speed = (int) (eleRequest.getScheRequest().getSpeed() * 1000);
        moveToFloor(getFloorNum(eleRequest.getScheRequest().getToFloor()));
        TimableOutput.println("OPEN-" + getFloorStr(eleFloor) + "-" + id);
        try {
            sleep(Constants.T_stop);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        TimableOutput.println("CLOSE-" + getFloorStr(eleFloor) + "-" + id);
        TimableOutput.println("SCHE-END-" + id);
        endTemporaryScheduling();
        eleRequest.setScheRequest(null);
    }

    public void personTemOutEle() {
        TimableOutput.println("OPEN-" + getFloorStr(eleFloor) + "-" + id);
        for (Integer i : eleMap.keySet()) {
            ArrayList<Person> temOutPersons = eleMap.get(i);
            for (Person person : temOutPersons) {
                elePersons.remove(person);
                if (person.getToFloor() == eleFloor) {
                    TimableOutput.println("OUT-S-" + person.getId() +
                            "-" + getFloorStr(eleFloor) + "-" + id);
                } else {
                    TimableOutput.println("OUT-F-" + person.getId() +
                            "-" + getFloorStr(eleFloor) + "-" + id);
                    person.setFromFloor(eleFloor);
                    eleRequest.addRequest(person);
                }
            }
        }
        eleMap.clear();
        try {
            sleep(Constants.OPEN_CLOSE_TIME);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        TimableOutput.println("CLOSE-" + getFloorStr(eleFloor) + "-" + id);
    }

    public void reverse() {
        direction = -direction;
    }

    public void move() {
        try {
            sleep(speed);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        Advice advice = strategy.getAdvice(eleFloor, elePersonNum, direction, eleMap, nowInSche);
        if (advice == Advice.OPEN) {
            openAndClose();
            try {
                sleep(Constants.OPEN_CLOSE_TIME);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        } else if (advice != Advice.MOVE) {
            return;
        }
        eleFloor += direction;
        TimableOutput.println("ARRIVE-" + getFloorStr(eleFloor) + "-" + id);
    }

    public void openAndClose() {
        TimableOutput.println("OPEN-" + getFloorStr(eleFloor) + "-" + id);
        outElevator();
        try {
            sleep(Constants.OPEN_CLOSE_TIME);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        Advice advice = strategy.getAdvice(eleFloor, elePersonNum, direction, eleMap, nowInSche);
        if (advice == Advice.REVERSE) {
            reverse();
        }
        inElevator();
        TimableOutput.println("CLOSE-" + getFloorStr(eleFloor) + "-" + id);
    }

    public void outElevator() {
        if (eleMap.containsKey(eleFloor)) {
            for (Person person : eleMap.get(eleFloor)) {
                if (person.getToFloor() == eleFloor) {
                    TimableOutput.println("OUT-S-" + person.getId() +
                            "-" + getFloorStr(eleFloor) + "-" + id);
                } else {
                    TimableOutput.println("OUT-F-" + person.getId() +
                            "-" + getFloorStr(eleFloor) + "-" + id);
                }
                elePersons.remove(person);
            }
            elePersonNum -= eleMap.get(eleFloor).size();
        }
        eleMap.remove(eleFloor, eleMap.get(eleFloor));
    }

    public void inElevator() {
        ArrayList<Person> inPerson = eleRequest.delRequest(eleFloor, direction, elePersonNum);
        inPerson.forEach(person -> {
            TimableOutput.println(String.format("IN-%d-%s-%d", person.getId(),
                    getFloorStr(eleFloor), id));
            eleMap.computeIfAbsent(person.getToFloor(), k -> new ArrayList<>()).add(person);
            elePersons.add(person);
        });
        elePersonNum += inPerson.size();
    }

    public void moveToFloor(int targetFloor) {
        if (targetFloor > eleFloor) {
            while (eleFloor != targetFloor) {
                try {
                    sleep(speed);
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
                eleFloor++;
                TimableOutput.println("ARRIVE-" + getFloorStr(eleFloor) + "-" + id);
            }
        } else if (targetFloor < eleFloor) {
            while (eleFloor != targetFloor) {
                try {
                    sleep(speed);
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
                eleFloor--;
                TimableOutput.println("ARRIVE-" + getFloorStr(eleFloor) + "-" + id);
            }
        } else {
            return;
        }
    }

    private void putFloorMap(String floorName, int floorIndex) {
        floorMap.put(floorName, floorIndex);
        floorMap.put(floorIndex, floorName);
    }

    private void addMap() {
        putFloorMap("B4", 1);
        putFloorMap("B3", 2);
        putFloorMap("B2", 3);
        putFloorMap("B1", 4);
        putFloorMap("F1", 5);
        putFloorMap("F2", 6);
        putFloorMap("F3", 7);
        putFloorMap("F4", 8);
        putFloorMap("F5", 9);
        putFloorMap("F6", 10);
        putFloorMap("F7", 11);
    }

    public static int getFloorNum(String currentFloor) {
        return (int) floorMap.get(currentFloor);
    }

    public static String getFloorStr(int floorNum) {
        return floorMap.get(floorNum).toString();
    }

    public int getEleId() {
        return id;
    }

    public int getEleFloor() {
        return eleFloor;
    }

    public int getElePersonNum() {
        return elePersonNum;
    }

    public int getDirection() {
        return direction;
    }

    public int getSpeed() {
        return speed;
    }

    public void setNowInSche(boolean nowInSche) {
        this.nowInSche = nowInSche;
    }

    public boolean isNowInSche() {
        return nowInSche;
    }

    // 判断电梯是否满人
    public boolean isFull() {
        return eleRequest.getPersonList().size() >= Constants.MAX_RECEIVE_NUM;
    }

    public void endTemporaryScheduling() {
        synchronized (this) { // 同步自身
            setNowInSche(false);
            speed = Constants.SPEED; // 恢复默认速度
        }
        synchronized (Schedule.getElevatorCondition()) { // 通知等待的调度线程
            Schedule.getElevatorCondition().notifyAll(); // 唤醒等待的线程
        }
    }
}
