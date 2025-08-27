import com.oocourse.elevator2.ScheRequest;
import java.util.stream.Collectors;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class RequestQueue {
    private boolean isEnd;
    private HashMap<Integer, HashSet<Person>> requestMap; // key是起始楼层，value是该起始楼层的乘客
    private List<Person> personList;
    private ScheRequest scheRequest; //临时调度请求
    private List<ScheRequest> scheRequests;

    public RequestQueue() {
        this.isEnd = false;
        this.requestMap = new HashMap<>();
        this.personList = new ArrayList<>();
        this.scheRequests = new ArrayList<>();
        this.scheRequest = null;
    }

    public synchronized boolean isAllFinished() {
        return personList.isEmpty() && scheRequest == null;
    }

    public synchronized boolean isScheEmpty() {
        return scheRequests.isEmpty();
    }

    public synchronized void setScheRequest(ScheRequest scheRequest) {
        this.scheRequest = scheRequest;
        notifyAll();
    }

    public synchronized ScheRequest getOneScheRequest() {
        if (scheRequests.isEmpty()) {
            return null;
        }
        ScheRequest scheRequest = scheRequests.get(0);
        scheRequests.remove(scheRequest);
        return scheRequest;
    }

    public synchronized ScheRequest getScheRequest() {
        return scheRequest;
    }

    public synchronized void addScheRequest(ScheRequest scheRequest) {
        scheRequests.add(scheRequest);
        notifyAll();
    }

    public synchronized void backToMainRequest(RequestQueue requestQueue) {
        List<Person> persons = requestQueue.getPersonList();
        if (persons.isEmpty()) {
            return;
        }

        // 批量添加到 personList
        personList.addAll(persons);

        // 按楼层分组批量更新 requestMap
        Map<Integer, Set<Person>> groupedPersons = persons.stream()
                .collect(Collectors.groupingBy(Person::getFromFloor, Collectors.toSet()));

        groupedPersons.forEach((floor, people) -> {
            requestMap.merge(floor, (HashSet<Person>) people, (existing, newSet) -> {
                existing.addAll(newSet);
                return existing;
            });
        });

        requestQueue.requestMap.clear();
        requestQueue.personList.clear();
        this.notifyAll();
    }

    public synchronized void addRequest(Person person) {
        addRequestHelper(person);
        personList.add(person);
        this.notifyAll();
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
        while (personList.isEmpty() && !isEnd && scheRequests.isEmpty()) {
            try {
                wait();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return null;
            }
        }
        if (personList.isEmpty() || !scheRequests.isEmpty()) {
            return null;
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

    public synchronized List<Person> getPersonList() {
        return personList;
    }
}
