import com.oocourse.library2.LibraryBookId;
import com.oocourse.library2.LibraryBookState;
import com.oocourse.library2.LibraryMoveInfo;
import com.oocourse.library2.LibraryTrace;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class BorrowReturnOffice {
    private final List<Book> books;
    private final BookShelf bookShelf;

    public BorrowReturnOffice(BookShelf bookShelf) {
        this.bookShelf = bookShelf;
        this.books = new ArrayList<>();
    }

    public void addBook(Book book) {
        books.add(book);
    }

    /**
     * 整理时图书从借还处移动至书架
     */
    public List<LibraryMoveInfo> moveBook2BookShelf(Map<LibraryBookId,
            List<LibraryTrace>> traces, LocalDate date) {
        List<LibraryMoveInfo> moves = new ArrayList<>();
        for (Book book : books) {
            moves.add(new LibraryMoveInfo(book.getId(), "bro", "bs"));
            bookShelf.addNormalBook(book);
            recordTraces(traces, book.getId(), date,
                    LibraryBookState.BORROW_RETURN_OFFICE, LibraryBookState.BOOKSHELF);
        }
        books.clear();
        return moves;
    }

    public void recordTraces(Map<LibraryBookId, List<LibraryTrace>> traces,
                             LibraryBookId bookId, LocalDate date,
                             LibraryBookState fromState, LibraryBookState toState) {
        traces.putIfAbsent(bookId, new ArrayList<>());
        LibraryTrace trace = new LibraryTrace(date, fromState, toState);
        traces.get(bookId).add(trace);
    }
}
