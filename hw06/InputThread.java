import com.oocourse.elevator2.ElevatorInput;
import com.oocourse.elevator2.PersonRequest;
import com.oocourse.elevator2.Request;
import com.oocourse.elevator2.ScheRequest;

import java.io.IOException;

public class InputThread extends Thread {
    private RequestQueue mainRequest;

    public InputThread(RequestQueue mainRequest) {
        this.mainRequest = mainRequest;
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
