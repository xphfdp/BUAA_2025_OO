public class Update {
    private int elevatorAId;
    private int elevatorBId;
    private TransferFloor transferFloor;

    public Update(int elevatorAId, int elevatorBId,TransferFloor floor) {
        this.elevatorAId = elevatorAId;
        this.elevatorBId = elevatorBId;
        this.transferFloor = floor;
    }

    public synchronized int getElevatorAId() {
        return elevatorAId;
    }

    public synchronized int getElevatorBId() {
        return elevatorBId;
    }

    public synchronized TransferFloor getTransferFloor() {
        return transferFloor;
    }
}
