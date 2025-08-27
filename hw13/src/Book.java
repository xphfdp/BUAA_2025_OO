import com.oocourse.library1.LibraryBookId;

import java.time.LocalDate;

public class Book {
    private final LibraryBookId id;
    private LocalDate orderedDate;

    public Book(LibraryBookId id) {
        this.id = id;
        this.orderedDate = null;
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

    /**
     * 判断书籍是否逾期
     */
    public boolean isExpired(LocalDate currentDate) {
        return currentDate.getDayOfYear() - orderedDate.getDayOfYear() >= 5;
    }
}
