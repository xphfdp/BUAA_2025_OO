import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class Strategy {
    private final RequestQueue request;

    public Strategy(RequestQueue request) {
        this.request = request;
    }

    public Advice getAdvice(int eleFloor, int elePersonNum, int eleDirection,
                            HashMap<Integer, ArrayList<Person>> eleMap, boolean nowInSche) {
        if (request.getUpdateRequest() != null) {
            return Advice.UPDATE;
        }
        if (request.getScheRequest() != null) {
            return Advice.SCHE;
        }
        if (openForOut(eleFloor, eleMap, elePersonNum)
                || openForIn(eleFloor, elePersonNum, eleDirection)) {
            return Advice.OPEN;
        }
        if (elePersonNum != 0) {
            return Advice.MOVE;
        }
        if (request.isEmpty()) {
            return request.isEnd() ? Advice.OVER : Advice.WAIT;
        } else {
            return reqSameDirection(eleFloor, eleDirection) ? Advice.MOVE : Advice.REVERSE;
        }
    }

    public boolean openForIn(int curFloor, int elePersonNum, int direction) {
        if (elePersonNum >= Constants.MAX_PERSON_NUM) {
            return false;
        }
        synchronized (request) {
            if (!request.isEmpty() && request.getReqMap().containsKey(curFloor)) {
                HashSet<Person> requestPersons = request.getReqMap().get(curFloor);
                for (Person person : requestPersons) {
                    if (person.getFromFloor() == curFloor && person.getDirection() == direction) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    public boolean openForOut(int curFloor, HashMap<Integer,
            ArrayList<Person>> eleMap, int curPersonNum) {
        return eleMap.containsKey(curFloor) && !eleMap.get(curFloor).isEmpty() && curPersonNum != 0;
    }

    public boolean reqSameDirection(int curFloor, int direction) {
        synchronized (request) {
            for (Integer i : request.getReqMap().keySet()) {
                if ((i - curFloor) * direction > 0) {
                    return true;
                }
            }
        }
        return false;
    }
}
