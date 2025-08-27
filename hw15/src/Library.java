import com.oocourse.library3.LibraryBookId;
import com.oocourse.library3.LibraryBookIsbn;
import com.oocourse.library3.LibraryCommand;
import com.oocourse.library3.LibraryTrace;
import com.oocourse.library3.LibraryOpenCmd;
import com.oocourse.library3.LibraryCloseCmd;
import com.oocourse.library3.LibraryReqCmd;
import com.oocourse.library3.LibraryMoveInfo;
import com.oocourse.library3.LibraryBookState;
import com.oocourse.library3.annotation.Trigger;
import com.oocourse.library3.LibraryQcsCmd;

import java.time.LocalDate;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Map;
import java.util.List;
import java.util.ArrayList;

import static com.oocourse.library3.LibraryIO.PRINTER;
import static com.oocourse.library3.LibraryIO.SCANNER;

public class Library {
    private final BookShelf bookShelf;
    private final AppointmentOffice appointmentOffice;
    private final BorrowReturnOffice borrowReturnOffice;
    private final ReadingRoom readingRoom;
    private final HashMap<String, User> users;
    private Map<LibraryBookId, List<LibraryTrace>> bookTraces;
    private LocalDate date;

    // 记录今天被阅读或者借阅的书籍的ISBN
    private HashSet<LibraryBookIsbn> todayReadOrBorrowedBooks;
    // 记录今天变成热门书籍的ISBN
    private HashSet<LibraryBookIsbn> todayHotBooks;

    public Library(BookShelf bookShelf, AppointmentOffice appointmentOffice,
                   BorrowReturnOffice borrowOffice, ReadingRoom readingRoom) {
        this.bookShelf = bookShelf;
        this.appointmentOffice = appointmentOffice;
        this.borrowReturnOffice = borrowOffice;
        this.readingRoom = readingRoom;
        this.users = new HashMap<>();
        this.bookTraces = new HashMap<>();
        this.todayReadOrBorrowedBooks = new HashSet<>();
        this.todayHotBooks = new HashSet<>();
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
                bookShelf.addNormalBook(new Book(bookId));
            }
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
            } else if (command instanceof LibraryQcsCmd) {
                LibraryQcsCmd qcs = (LibraryQcsCmd) command;
                String studentId = qcs.getStudentId();
                users.putIfAbsent(studentId, new User(studentId));
                User user = users.get(studentId);
                PRINTER.info(command, user.getCreditScore());
            }
            else {
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
                } else if (req.getType().equals(LibraryReqCmd.Type.READ)) {
                    handleRead(req);
                } else if (req.getType().equals(LibraryReqCmd.Type.RESTORED)) {
                    handleRestored(req);
                }
            }
        }
    }

    /**
     * 开馆时整理书籍
     */
    private void sortBooksDay() {
        todayHotBooks = new HashSet<>(todayReadOrBorrowedBooks);
        List<LibraryMoveInfo> allMovesForDay = new ArrayList<>();
        List<LibraryMoveInfo> expiredMoves =
                appointmentOffice.moveBooks2BookShelf(bookTraces,date, users);
        List<LibraryMoveInfo> sortBookShelfMoves =
                bookShelf.sortBooks(bookTraces, date, todayHotBooks);
        List<LibraryMoveInfo> orderedMoves = appointmentOffice.handleReqCmd(bookTraces, date);
        allMovesForDay.addAll(expiredMoves);
        allMovesForDay.addAll(sortBookShelfMoves);
        allMovesForDay.addAll(orderedMoves);
        // 用户持有书籍的逾期检查
        for (User user : users.values()) {
            HashSet<Book> userBooks = new HashSet<>(user.getHeldBooks());
            for (Book book : userBooks) {
                if (book.getBorrowedDate() != null) {
                    LocalDate dueDate = book.getBorrowedDate();
                    if (this.date.isAfter(dueDate)) {
                        LocalDate lastProcessedDate = book.getLastProcessedDate();
                        if (lastProcessedDate == null || lastProcessedDate.isBefore(dueDate)) {
                            lastProcessedDate = dueDate;
                        }
                        LocalDate dayToPenalizeIterator = lastProcessedDate.plusDays(1);
                        while (!dayToPenalizeIterator.isAfter(this.date)) {
                            user.addCreditScore(-5);
                            if (dayToPenalizeIterator.equals(this.date)) {
                                break;
                            }
                            dayToPenalizeIterator = dayToPenalizeIterator.plusDays(1);
                        }
                        book.setLastProcessedDate(this.date);
                    }
                }
            }
        }
        todayReadOrBorrowedBooks.clear();
        PRINTER.move(date, allMovesForDay);
    }

    /**
     * 闭馆时整理书籍
     */
    private void sortBooksNight() {
        List<LibraryMoveInfo> sortBorrowReturnOfficeMoves =
                borrowReturnOffice.moveBook2BookShelf(bookTraces, date);
        List<LibraryMoveInfo> sortReadingRoomMoves =
                readingRoom.moveBooks2BookShelf(bookTraces, date, users);
        List<LibraryMoveInfo> moves = new ArrayList<>();
        moves.addAll(sortBorrowReturnOfficeMoves);
        moves.addAll(sortReadingRoomMoves);
        todayHotBooks.clear();
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
    @Trigger(from = "InitState", to = "Borrow")
    private void handleBorrow(LibraryReqCmd req) {
        LibraryBookIsbn bookIsbn = req.getBookIsbn();
        String userId = req.getStudentId();
        User user = users.get(userId);
        if ((bookIsbn.isTypeB() || bookIsbn.isTypeC()) && !(user.getCreditScore() >= 60)) {
            PRINTER.reject(req);
            return;
        }
        Book book = null;
        for (Book book1 : bookShelf.getBooks()) {
            if (book1.getId().getBookIsbn().equals(bookIsbn)) {
                book = book1;
                break;
            }
        }
        if (book == null) {
            PRINTER.reject(req);
        } else if (book.getId().isTypeA()) {
            PRINTER.reject(req);
        } else {
            if (user.canBorrowOrOrder(book.getId())) {
                user.addBook(book);
                book.setBorrowedDate(date);
                boolean isHotBook = bookShelf.isHotBook(book);
                bookShelf.removeBook(book);
                if (isHotBook) {
                    recordTrace(book.getId(), date, LibraryBookState.HOT_BOOKSHELF,
                            LibraryBookState.USER);
                } else {
                    recordTrace(book.getId(), date, LibraryBookState.BOOKSHELF,
                            LibraryBookState.USER);
                }
                todayReadOrBorrowedBooks.add(bookIsbn);
                PRINTER.accept(req, book.getId());
            } else {
                PRINTER.reject(req);
            }
        }
    }

    /**
     * 处理还书（指借阅/取书后归还书籍）动作
     */
    @Trigger(from = "Borrow", to = "Return")
    private void handleReturn(LibraryReqCmd req) {
        LibraryBookId bookId = req.getBookId();
        String userId = req.getStudentId();
        User user = users.get(userId);
        Book book = user.getBook(bookId);
        user.removeBook(book);
        borrowReturnOffice.addBook(book);
        recordTrace(bookId, date, LibraryBookState.USER, LibraryBookState.BORROW_RETURN_OFFICE);
        // PRINTER.accept(req);
        if (req.getDate().isAfter(book.getBorrowedDate())) {
            // int days = (int) ChronoUnit.DAYS.between(book.getBorrowedDate(), date);
            // user.addCreditScore(-days * 5);
            // user.addCreditScore(5);
            PRINTER.accept(req, "overdue");
        } else {
            user.addCreditScore(10);
            PRINTER.accept(req, "not overdue");
        }
    }

    /**
     * 处理预约动作
     */
    @Trigger(from = "InitState", to = "Order")
    private void handleOrder(LibraryReqCmd req) {
        LibraryBookIsbn bookIsbn = req.getBookIsbn();
        String userId = req.getStudentId();
        User user = users.get(userId);
        if ((bookIsbn.isTypeB() || bookIsbn.isTypeC()) && !(user.getCreditScore() >= 100)) {
            PRINTER.reject(req);
            return;
        }
        if (appointmentOffice.hasUnpickedBooks(userId) ||
                appointmentOffice.hasPendingOrder(userId)) {
            PRINTER.reject(req);
        } else if (user.canBorrowOrOrder(bookIsbn)) {
            appointmentOffice.addReqCmd(req);
            PRINTER.accept(req);
        } else {
            PRINTER.reject(req);
        }
    }

    /**
     * 处理取书动作
     */
    @Trigger(from = "Order", to = "Borrow")
    private void handlePicked(LibraryReqCmd req) {
        LibraryBookIsbn bookIsbn = req.getBookIsbn();
        String userId = req.getStudentId();
        User user = users.get(userId);
        if (user.canBorrowOrOrder(bookIsbn)) {
            Book book = appointmentOffice.getBook4User(userId, bookIsbn);
            if (book == null) {
                PRINTER.reject(req);
            } else {
                appointmentOffice.removeBook(userId, book);
                user.addBook(book);
                book.setBorrowedDate(date);
                recordTrace(book.getId(), date, LibraryBookState.APPOINTMENT_OFFICE,
                        LibraryBookState.USER);
                PRINTER.accept(req, book.getId());
            }
        } else {
            PRINTER.reject(req);
        }
    }

    /**
     * 处理阅读动作
     */
    @Trigger(from = "InitState", to = "Read")
    private void handleRead(LibraryReqCmd req) {
        LibraryBookIsbn bookIsbn = req.getBookIsbn();
        String userId = req.getStudentId();
        User user = users.get(userId);
        if ((bookIsbn.getType() == LibraryBookIsbn.Type.A && user.getCreditScore() < 40) ||
                ((bookIsbn.getType() == LibraryBookIsbn.Type.B ||
                        bookIsbn.getType() == LibraryBookIsbn.Type.C)) &&
                        !(user.getCreditScore() > 0)) {
            PRINTER.reject(req);
            return;
        }
        if (readingRoom.getReadingBooks().containsKey(userId)) {
            // 某用户存在当日未读完的书籍
            PRINTER.reject(req);
        } else {
            Book book = null;
            for (Book book1 : bookShelf.getBooks()) {
                if (book1.getId().getBookIsbn().equals(bookIsbn)) {
                    book = book1;
                    break;
                }
            }
            if (book == null) {
                // 无余本在架
                PRINTER.reject(req);
            } else {
                // 书籍从bs/hbs移动到rr
                boolean isHotBook = bookShelf.isHotBook(book);
                bookShelf.removeBook(book);
                readingRoom.addReadingBook(userId, book);
                if (isHotBook) {
                    recordTrace(book.getId(), date, LibraryBookState.HOT_BOOKSHELF,
                            LibraryBookState.READING_ROOM);
                } else {
                    recordTrace(book.getId(), date, LibraryBookState.BOOKSHELF,
                            LibraryBookState.READING_ROOM);
                }
                todayReadOrBorrowedBooks.add(bookIsbn);
                PRINTER.accept(req, book.getId());
            }
        }
    }

    /**
     * 处理归还（指阅读后归还书籍）动作
     * 归还后书籍从rr移动到bro
     */
    @Trigger(from = "Read", to = "Restore")
    private void handleRestored(LibraryReqCmd req) {
        LibraryBookId bookId = req.getBookId();
        String userId = req.getStudentId();
        User user = users.get(userId);
        Book book = readingRoom.getCertainBook(userId);
        if (book != null) { // 实际上一定不为null
            readingRoom.removeReadingBook(userId);
            borrowReturnOffice.addBook(book);
            recordTrace(bookId, date, LibraryBookState.READING_ROOM,
                    LibraryBookState.BORROW_RETURN_OFFICE);
            user.addCreditScore(10); // 阅读后当日归还立即+10分
            PRINTER.accept(req);
        }
    }

    /*-----------------------------------helper methods------------------------------------------*/
    private void recordTrace(LibraryBookId bookId, LocalDate date,
                             LibraryBookState fromState, LibraryBookState toState) {
        this.bookTraces.putIfAbsent(bookId, new ArrayList<>());
        LibraryTrace trace = new LibraryTrace(date, fromState, toState);
        this.bookTraces.get(bookId).add(trace);
    }
}
