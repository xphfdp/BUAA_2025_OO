import com.oocourse.elevator3.ElevatorInput;
import com.oocourse.elevator3.PersonRequest;
import com.oocourse.elevator3.Request;
import com.oocourse.elevator3.ScheRequest;
import com.oocourse.elevator3.UpdateRequest;

import java.io.IOException;

public class InputThread extends Thread {
    private RequestQueue mainRequest;
    private Schedule schedule;

    public InputThread(Schedule schedule) {
        this.mainRequest = Schedule.getMainRequestTable();
        this.schedule = schedule;
        this.schedule.start();
    }

    @Override
    public void run() {
        ElevatorInput elevatorInput = new ElevatorInput(System.in);
        while (true) {
            Request request = elevatorInput.nextRequest();
            if (request != null) {
                if (request instanceof PersonRequest) {
                    PersonRequest personRequest = (PersonRequest) request;
                    Person person = new Person(personRequest);
                    mainRequest.addRequest(person);
                } else if (request instanceof ScheRequest) {
                    ScheRequest scheRequest = (ScheRequest) request;
                    mainRequest.addScheRequest(scheRequest);
                } else if (request instanceof UpdateRequest) {
                    UpdateRequest updateRequest = (UpdateRequest) request;
                    TransferFloor transferFloor = new TransferFloor(
                            Elevator.getFloorNum(updateRequest.getTransferFloor()));
                    Update update = new Update(updateRequest.getElevatorAId(),
                            updateRequest.getElevatorBId(),transferFloor);
                    mainRequest.addUpdateRequest(update);
                }
            } else {
                mainRequest.setEnd(true);
                break;
            }
        }
        try {
            elevatorInput.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
