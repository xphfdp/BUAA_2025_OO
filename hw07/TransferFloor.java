public class TransferFloor {
    private int readyCount;
    private int endCount;
    private int transferFloor;
    private boolean isOccupied;

    public TransferFloor(int transferFloor) {
        this.readyCount = 0;
        this.endCount = 0;
        this.transferFloor = transferFloor;
        this.isOccupied = false;
    }

    public synchronized void isReady() {
        readyCount++;
        if (readyCount == 2) {
            notifyAll();
        } else {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
    }

    public synchronized void isEnd() {
        endCount++;
        if (endCount == 2) {
            notifyAll();
        } else {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
    }

    public synchronized void setOccupied() {
        if (isOccupied) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        isOccupied = true;
    }

    public synchronized void setEmpty() {
        isOccupied = false;
        notifyAll();
    }

    public synchronized int getTransferFloor() {
        return transferFloor;
    }
}
