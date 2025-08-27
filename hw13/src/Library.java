import com.oocourse.library1.LibraryBookId;
import com.oocourse.library1.LibraryBookIsbn;
import com.oocourse.library1.LibraryCommand;
import com.oocourse.library1.LibraryTrace;
import com.oocourse.library1.LibraryOpenCmd;
import com.oocourse.library1.LibraryCloseCmd;
import com.oocourse.library1.LibraryReqCmd;
import com.oocourse.library1.LibraryMoveInfo;
import com.oocourse.library1.LibraryBookState;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static com.oocourse.library1.LibraryIO.PRINTER;
import static com.oocourse.library1.LibraryIO.SCANNER;

public class Library {
    private final BookShelf bookShelf;
    private final AppointmentOffice appointmentOffice;
    private final BorrowReturnOffice borrowReturnOffice;
    private final HashMap<String, User> users;
    private Map<LibraryBookId, List<LibraryTrace>> bookTraces;
    private LocalDate date;

    public Library(BookShelf bookShelf, AppointmentOffice appointmentOffice,
                   BorrowReturnOffice borrowOffice) {
        this.bookShelf = bookShelf;
        this.appointmentOffice = appointmentOffice;
        this.borrowReturnOffice = borrowOffice;
        this.users = new HashMap<>();
        this.bookTraces = new HashMap<>();
    }

    public void run() {
        Map<LibraryBookIsbn, Integer> inventory = SCANNER.getInventory();
        for (Map.Entry<LibraryBookIsbn, Integer> entry : inventory.entrySet()) {
            LibraryBookIsbn isbn = entry.getKey();
            int numberOfCopies = entry.getValue();
            LibraryBookIsbn.Type type = isbn.getType();
            String uid = isbn.getUid();
            for (int i = 1;i <= numberOfCopies;i++) {
                String copyId = String.format("%02d", i);
                LibraryBookId bookId = new LibraryBookId(type, uid, copyId);
                bookShelf.addBook(new Book(bookId));
            }
            //for (int i = 0; i < entry.getValue(); i++) {
            //    bookShelf.addBook(new Book(entry.getKey()));
            //}
        }

        while (true) {
            LibraryCommand command = SCANNER.nextCommand();
            if (command == null) {
                break;
            }
            date = command.getDate();

            if (command instanceof LibraryOpenCmd) {
                sortBooksDay();
            } else if (command instanceof LibraryCloseCmd) {
                sortBooksNight();
            } else {
                LibraryReqCmd req = (LibraryReqCmd) command;
                String userId = req.getStudentId();
                users.putIfAbsent(userId, new User(userId));

                if (req.getType().equals(LibraryReqCmd.Type.QUERIED)) {
                    handleQuery(req);
                } else if (req.getType().equals(LibraryReqCmd.Type.BORROWED)) {
                    handleBorrow(req);
                } else if (req.getType().equals(LibraryReqCmd.Type.RETURNED)) {
                    handleReturn(req);
                } else if (req.getType().equals(LibraryReqCmd.Type.ORDERED)) {
                    handleOrder(req);
                } else if (req.getType().equals(LibraryReqCmd.Type.PICKED)) {
                    handlePicked(req);
                }
            }
        }
    }

    /**
     * 开馆时整理书籍
     */
    private void sortBooksDay() {
        //List<LibraryMoveInfo> moves = new ArrayList<>();
        //moves.addAll(appointmentOffice.moveBooks2BookShelf(date));
        //moves.addAll(appointmentOffice.handleReqCmd(date));
        //PRINTER.move(date, moves);
        List<LibraryMoveInfo> allMovesForDay = new ArrayList<>();
        List<LibraryMoveInfo> expiredMoves = appointmentOffice.moveBooks2BookShelf(bookTraces,date);
        allMovesForDay.addAll(expiredMoves);
        List<LibraryMoveInfo> orderedMoves = appointmentOffice.handleReqCmd(bookTraces, date);
        allMovesForDay.addAll(orderedMoves);
        PRINTER.move(date, allMovesForDay);
    }

    /**
     * 闭馆时整理书籍
     */
    private void sortBooksNight() {
        List<LibraryMoveInfo> sortMoves = borrowReturnOffice.moveBook2BookShelf(bookTraces, date);
        List<LibraryMoveInfo> moves = new ArrayList<>();
        moves.addAll(sortMoves);
        PRINTER.move(date, moves);
    }

    /**
     * 处理查询动作
     */
    private void handleQuery(LibraryReqCmd req) {
        LibraryBookId bookId = req.getBookId();
        List<LibraryTrace> traces = this.bookTraces.get(bookId);
        LocalDate queryDate = req.getDate();
        if (traces == null) {
            traces = new ArrayList<>();
        }
        PRINTER.info(queryDate, bookId, traces);
    }

    /**
     * 处理借书动作
     */
    private void handleBorrow(LibraryReqCmd req) {
        //LibraryBookId bookId = req.getBookId();
        LibraryBookIsbn bookIsbn = req.getBookIsbn();
        String userId = req.getStudentId();
        User user = users.get(userId);
        Book book = null;
        //Book book = bookShelf.getBook(bookId);
        for (Book book1 : bookShelf.getBooks()) {
            if (book1.getId().getBookIsbn().equals(bookIsbn)) {
                book = book1;
                break;
            }
        }
        if (book == null) {
            PRINTER.reject(req);
            //PRINTER.reject(date, req.getType(), userId, bookId.getBookIsbn());
        } else if (book.getId().isTypeA()) {
            PRINTER.reject(req);
            //PRINTER.reject(date, req.getType(), userId, bookId.getBookIsbn());
        } else {
            if (user.canBorrowOrOrder(book.getId())) {
                user.addBook(book);
                bookShelf.removeBook(book);
                recordTrace(book.getId(), date, LibraryBookState.BOOKSHELF, LibraryBookState.USER);
                PRINTER.accept(req, book.getId());
                //PRINTER.accept(date, req.getType(), userId, bookId);
            } else {
                PRINTER.reject(req);
                //PRINTER.reject(date, req.getType(), userId, bookId.getBookIsbn());
            }
        }
    }

    /**
     * 处理还书动作
     */
    private void handleReturn(LibraryReqCmd req) {
        LibraryBookId bookId = req.getBookId();
        String userId = req.getStudentId();
        User user = users.get(userId);
        Book book = user.getBook(bookId);
        user.removeBook(book);
        borrowReturnOffice.addBook(book);
        recordTrace(bookId, date, LibraryBookState.USER, LibraryBookState.BORROW_RETURN_OFFICE);
        PRINTER.accept(req);
        //PRINTER.accept(date, req.getType(), userId, bookId);
    }

    /**
     * 处理预约动作
     */
    private void handleOrder(LibraryReqCmd req) {
        LibraryBookIsbn bookIsbn = req.getBookIsbn();
        String userId = req.getStudentId();
        User user = users.get(userId);
        if (appointmentOffice.hasUnpickedBooks(userId) ||
                appointmentOffice.hasPendingOrder(userId)) {
            PRINTER.reject(req);
            //PRINTER.reject(date, req.getType(), userId, bookId.getBookIsbn());
        } else if (user.canBorrowOrOrder(bookIsbn)) {
            appointmentOffice.addReqCmd(req);
            PRINTER.accept(req);
            //PRINTER.accept(date, req.getType(), userId, bookId.getBookIsbn());
        } else {
            PRINTER.reject(req);
            //PRINTER.reject(date, req.getType(), userId, bookId.getBookIsbn());
        }
    }

    /**
     * 处理取书动作
     */
    private void handlePicked(LibraryReqCmd req) {
        //LibraryBookId bookId = req.getBookId();
        LibraryBookIsbn bookIsbn = req.getBookIsbn();
        String userId = req.getStudentId();
        User user = users.get(userId);
        if (user.canBorrowOrOrder(bookIsbn)) {
            Book book = appointmentOffice.getBook4User(userId, bookIsbn);
            if (book == null) {
                PRINTER.reject(req);
                //PRINTER.reject(date, req.getType(), userId, bookId.getBookIsbn());
            } else {
                appointmentOffice.removeBook(userId, book);
                user.addBook(book);
                recordTrace(book.getId(), date, LibraryBookState.APPOINTMENT_OFFICE,
                        LibraryBookState.USER);
                PRINTER.accept(req, book.getId());
                //PRINTER.accept(date, req.getType(), userId, bookId);
            }
        } else {
            PRINTER.reject(req);
            //PRINTER.reject(date, req.getType(), userId, bookId.getBookIsbn());
        }
    }

    private void recordTrace(LibraryBookId bookId, LocalDate date,
                             LibraryBookState fromState, LibraryBookState toState) {
        this.bookTraces.putIfAbsent(bookId, new ArrayList<>());
        LibraryTrace trace = new LibraryTrace(date, fromState, toState);
        this.bookTraces.get(bookId).add(trace);
    }
}
