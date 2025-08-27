import com.oocourse.elevator1.PersonRequest;

public class Person {
    private int id;
    private int fromFloor;
    private int toFloor;
    private int elevatorId;
    private int priority;
    private String fromFloorName;
    private String toFloorName;
    private int direction;

    public Person(PersonRequest request) {
        this.id = request.getPersonId();
        this.fromFloor = Elevator.getFloorNum(request.getFromFloor());
        this.toFloor = Elevator.getFloorNum(request.getToFloor());
        this.fromFloorName = request.getFromFloor();
        this.toFloorName = request.getToFloor();
        this.elevatorId = request.getElevatorId();
        this.priority = request.getPriority();
        this.direction = (toFloor > fromFloor) ? 1 : -1;
    }

    public int getFromFloor() {
        return fromFloor;
    }

    public int getToFloor() {
        return toFloor;
    }

    public int getId() {
        return id;
    }

    public int getElevatorId() {
        return elevatorId;
    }

    public int getDirection() {
        return direction;
    }

    public int getPriority() {
        return priority;
    }

    public String getFromFloorName() {
        return fromFloorName;
    }

    public String getToFloorName() {
        return toFloorName;
    }
}
