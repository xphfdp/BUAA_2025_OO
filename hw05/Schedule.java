import java.util.ArrayList;

public class Schedule extends Thread {

    private RequestQueue mainRequestTable;
    private ArrayList<RequestQueue> subRequestQueues;

    public Schedule(RequestQueue mainRequestTable,
                    ArrayList<RequestQueue> verticalRequestTables) {
        this.mainRequestTable = mainRequestTable;
        this.subRequestQueues = verticalRequestTables;

    }

    @Override
    public void run() {
        while (true) {
            if (mainRequestTable.isEmpty() && mainRequestTable.isEnd()) {
                for (RequestQueue requestTable : subRequestQueues) {
                    requestTable.setEnd(true);
                }
                return;
            }
            Person person = mainRequestTable.getOneRequest();
            if (person == null) {
                continue;
            }
            int elevatorId = person.getElevatorId() - 1;
            subRequestQueues.get(elevatorId).addRequest(person);
        }
    }
}
