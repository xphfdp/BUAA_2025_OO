import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class RequestQueue {
    private boolean isEnd;
    private HashMap<Integer, HashSet<Person>> requestMap; // key是起始楼层，value是该起始楼层的乘客
    private List<Person> personList;

    public RequestQueue() {
        this.isEnd = false;
        this.requestMap = new HashMap<>();
        this.personList = new ArrayList<>();
    }

    public synchronized void addRequest(Person person) {
        addRequestHelper(person);
        personList.add(person);
        synchronized (this) {
            this.notifyAll();
        }
    }

    private void addRequestHelper(Person person) {
        requestMap.computeIfAbsent(person.getFromFloor(), k -> new HashSet<>()).add(person);
    }

    public synchronized ArrayList<Person> delRequest(int fromFloor,
                                                     int eleDirection, int elePersonNum) {
        ArrayList<Person> inPerson = new ArrayList<>();
        if (elePersonNum >= Constants.MAX_PERSON_NUM) {
            return inPerson;
        }
        int canInNum = Constants.MAX_PERSON_NUM - elePersonNum;
        HashSet<Person> persons = requestMap.get(fromFloor);
        if (persons != null) {
            List<Person> toAdd = persons.stream()
                    .filter(person -> (person.getToFloor() - fromFloor) * eleDirection > 0)
                    .limit(canInNum)
                    .collect(Collectors.toList());
            inPerson.addAll(toAdd);
            persons.removeAll(toAdd);
            personList.removeAll(toAdd);
            if (persons.isEmpty()) {
                requestMap.remove(fromFloor);
            }
        }
        return inPerson;
    }

    public synchronized Person getOneRequest() {
        while (personList.isEmpty() && !isEnd) {
            try {
                wait();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return null;
            }
        }
        if (!personList.isEmpty()) {
            Person person = personList.remove(0); // 直接移除并获取第一个元素
            int perFloor = person.getFromFloor();
            updateRequestMap(person, perFloor);
            return person;
        }
        return null;
    }

    private void updateRequestMap(Person person, int perFloor) {
        Set<Person> requests = requestMap.get(perFloor);
        if (requests != null) {
            requests.remove(person);
            if (requests.isEmpty()) {
                requestMap.remove(perFloor);
            }
        }
    }

    public synchronized boolean isEmpty() {
        return requestMap.isEmpty();
    }

    public synchronized boolean isEnd() {
        return isEnd;
    }

    public synchronized void setEnd(boolean end) {
        isEnd = end;
        this.notifyAll();
    }

    public synchronized HashMap<Integer, HashSet<Person>> getReqMap() {
        return requestMap;
    }

}
