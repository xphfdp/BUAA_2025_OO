import com.oocourse.library3.LibraryBookId;

import java.time.LocalDate;
import java.time.temporal.ChronoUnit;

public class Book {
    private final LibraryBookId id;
    private LocalDate orderedDate;
    private LocalDate borrowedDate;
    private LocalDate lastProcessedDate;

    public Book(LibraryBookId id) {
        this.id = id;
        this.orderedDate = null;
        this.borrowedDate = null;
        this.lastProcessedDate = null;
    }

    public LibraryBookId getId() {
        return id;
    }

    public LibraryBookId.Type getType() {
        return id.getType();
    }

    public boolean isTypeB() {
        return getType() == LibraryBookId.Type.B;
    }

    public void setOrderedDate(LocalDate orderedDate) {
        this.orderedDate = orderedDate;
    }

    public void setBorrowedDate(LocalDate borrowedDate) {
        this.borrowedDate = borrowedDate.plusDays(getBorrowPeriod());
        this.lastProcessedDate = this.borrowedDate;
    }

    /**
     * 判断被预约的书籍是否逾期
     */
    public boolean isExpired(LocalDate currentDate) {
        long daysBetween = ChronoUnit.DAYS.between(orderedDate, currentDate);
        return daysBetween >= 5;
    }

    public LocalDate getBorrowedDate() {
        return borrowedDate;
    }

    public int getBorrowPeriod() {
        if (getType() == LibraryBookId.Type.B) {
            return 30;
        } else {
            return 60;
        }
    }

    public LocalDate getLastProcessedDate() {
        return lastProcessedDate;
    }

    public void setLastProcessedDate(LocalDate date) {
        this.lastProcessedDate = date;
    }
}
