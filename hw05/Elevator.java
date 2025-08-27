import com.oocourse.elevator1.TimableOutput;

import java.util.ArrayList;
import java.util.HashMap;

public class Elevator extends Thread {
    private int id;
    private int elePersonNum;
    private int eleFloor;
    private int direction;
    private RequestQueue eleRequest;
    private Strategy strategy;
    private static HashMap<Object, Object> floorMap = new HashMap<>(); //楼层映射表
    private static int floorNum = 11;
    private HashMap<Integer, ArrayList<Person>> eleMap; // key是目标楼层，value是要到达该楼层的乘客列表

    public Elevator(int id, RequestQueue eleRequest) {
        this.id = id;
        this.elePersonNum = Constants.ORIGIN_PERSON_NUM;
        this.eleFloor = Constants.ORIGIN_FLOOR_NUM;
        this.direction = 1;
        this.eleMap = new HashMap<>();
        this.strategy = new Strategy(eleRequest);
        this.eleRequest = eleRequest;
        addMap();
    }

    @Override
    public void run() {
        while (true) {
            Advice advice = strategy.getAdvice(eleFloor, elePersonNum, direction, eleMap);
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

    public void reverse() {
        direction = -direction;
    }

    public void move() {
        try {
            sleep(Constants.SPEED);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        Advice advice = strategy.getAdvice(eleFloor, elePersonNum, direction, eleMap);
        if (advice == Advice.OPEN) {
            openAndClose();
            try {
                sleep(Constants.OPEN_CLOSE_TIME);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
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
        Advice advice = strategy.getAdvice(eleFloor, elePersonNum, direction, eleMap);
        if (advice == Advice.REVERSE) {
            reverse();
        }
        inElevator();
        TimableOutput.println("CLOSE-" + getFloorStr(eleFloor) + "-" + id);
    }

    public void outElevator() {
        if (eleMap.containsKey(eleFloor)) {
            for (Person person : eleMap.get(eleFloor)) {
                TimableOutput.println("OUT-" + person.getId() + "-" + getFloorStr(eleFloor)
                        + "-" + id);
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
        });
        elePersonNum += inPerson.size();
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
}
