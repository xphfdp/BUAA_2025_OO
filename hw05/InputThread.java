import com.oocourse.elevator1.ElevatorInput;
import com.oocourse.elevator1.PersonRequest;
import com.oocourse.elevator1.Request;

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
                }
            } else {
                mainRequest.setEnd(true);
                break;
            }
        }
    }
}
