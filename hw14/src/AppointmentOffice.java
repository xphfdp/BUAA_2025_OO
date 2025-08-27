import com.oocourse.library2.LibraryBookId;
import com.oocourse.library2.LibraryBookIsbn;
import com.oocourse.library2.LibraryMoveInfo;
import com.oocourse.library2.LibraryReqCmd;
import com.oocourse.library2.LibraryTrace;
import com.oocourse.library2.LibraryBookState;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class AppointmentOffice {
    private HashMap<String, List<Book>> orders;
    private List<LibraryReqCmd> reqCmds;
    private BookShelf bookShelf;

    public AppointmentOffice(BookShelf bookShelf) {
        this.bookShelf = bookShelf;
        orders = new HashMap<>();
        reqCmds = new ArrayList<>();
    }

    public void addReqCmd(LibraryReqCmd reqCmd) {
        reqCmds.add(reqCmd);
    }

    /**
     * 用户从预约处取书
     */
    public Book getBook4User(String userId, LibraryBookIsbn bookIsbn) {
        if (!orders.containsKey(userId)) {
            return null;
        }
        List<Book> books = orders.get(userId);
        for (Book book : books) {
            if (book.getId().getBookIsbn().equals(bookIsbn)) {
                return book;
            }
        }
        return null;
    }

    public void removeBook(String userId, Book book) {
        orders.get(userId).remove(book);
    }

    /**
     * 处理逾期书籍，从预约处整理到书架
     */
    public List<LibraryMoveInfo> moveBooks2BookShelf(Map<LibraryBookId,
            List<LibraryTrace>> traces, LocalDate date) {
        List<LibraryMoveInfo> moves = new ArrayList<>();
        for (List<Book> books : orders.values()) {
            List<Book> books2Move = new ArrayList<>();
            for (Book book : books) {
                if (book.isExpired(date)) {
                    moves.add(new LibraryMoveInfo(book.getId(), "ao", "bs"));
                    recordTraces(traces, book.getId(), date, LibraryBookState.APPOINTMENT_OFFICE,
                            LibraryBookState.BOOKSHELF);
                    books2Move.add(book);
                    bookShelf.addNormalBook(book);
                }
            }
            books.removeAll(books2Move);
        }
        return moves;
    }

    /**
     * 处理用户预约请求
     */
    public List<LibraryMoveInfo> handleReqCmd(Map<LibraryBookId,
            List<LibraryTrace>> traces, LocalDate date) {
        List<LibraryMoveInfo> moves = new ArrayList<>();
        List<LibraryReqCmd> fulfilledCmds = new ArrayList<>();
        for (LibraryReqCmd reqCmd : reqCmds) {
            LibraryBookIsbn bookIsbn = reqCmd.getBookIsbn();
            String userId = reqCmd.getStudentId();
            Book book = null;
            for (Book book1 : bookShelf.getBooks()) {
                if (book1.getId().getBookIsbn().equals(bookIsbn)) {
                    book = book1;
                    break;
                }
            }
            if (book != null) {
                boolean isHotBook = bookShelf.isHotBook(book);
                bookShelf.removeBook(book);
                orders.putIfAbsent(userId, new ArrayList<>());
                boolean isHotBook2 = isHotBook;
                orders.get(userId).add(book);
                book.setOrderedDate(date);
                if (isHotBook2) {
                    recordTraces(traces, book.getId(), date, LibraryBookState.HOT_BOOKSHELF,
                            LibraryBookState.APPOINTMENT_OFFICE);
                    moves.add(new LibraryMoveInfo(book.getId(), "hbs", "ao", userId));
                } else {
                    recordTraces(traces, book.getId(), date, LibraryBookState.BOOKSHELF,
                            LibraryBookState.APPOINTMENT_OFFICE);
                    moves.add(new LibraryMoveInfo(book.getId(), "bs", "ao", userId));
                }
                fulfilledCmds.add(reqCmd);
            }
        }
        reqCmds.removeAll(fulfilledCmds);
        return moves;
    }

    /**
     * 检查预约处是否存在用户已预约但是未取走的书
     */
    public boolean hasUnpickedBooks(String userId) {
        return orders.containsKey(userId) && !orders.get(userId).isEmpty();
    }

    /**
     * 检查用户是否有已经成功提交、但未被整理至预约处的请求
     */
    public boolean hasPendingOrder(String userId) {
        for (LibraryReqCmd cmd : reqCmds) {
            if (cmd.getStudentId().equals(userId)) {
                return true;
            }
        }
        return false;
    }

    /**
     * 记录书籍状态变迁
     */
    public void recordTraces(Map<LibraryBookId, List<LibraryTrace>> traces,
                             LibraryBookId bookId, LocalDate date,
                             LibraryBookState fromState, LibraryBookState toState) {
        traces.putIfAbsent(bookId, new ArrayList<>());
        LibraryTrace trace = new LibraryTrace(date, fromState, toState);
        traces.get(bookId).add(trace);
    }
}
