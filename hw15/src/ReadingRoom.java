import com.oocourse.library3.LibraryBookId;
import com.oocourse.library3.LibraryBookState;
import com.oocourse.library3.LibraryMoveInfo;
import com.oocourse.library3.LibraryTrace;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class ReadingRoom {
    private final HashMap<String, Book> userReadingBooks; // 某一用户阅读的书籍
    private final BookShelf bookShelf;

    public ReadingRoom(BookShelf bookshelf) {
        userReadingBooks = new HashMap<String, Book>();
        this.bookShelf = bookshelf;
    }

    public void addReadingBook(String userId, Book book) {
        userReadingBooks.put(userId, book);
    }

    public HashMap<String, Book> getReadingBooks() {
        return userReadingBooks;
    }

    public Book getCertainBook(String userId) {
        return userReadingBooks.getOrDefault(userId, null);
    }

    public void removeReadingBook(String userId) {
        userReadingBooks.remove(userId);
    }

    /**
     * 整理时将未被归还的书籍移动到书架
     */
    public List<LibraryMoveInfo> moveBooks2BookShelf(Map<LibraryBookId,
            List<LibraryTrace>> traces, LocalDate date, HashMap<String, User> users) {
        List<LibraryMoveInfo> moveInfos = new ArrayList<>();
        for (String userId : users.keySet()) {
            User user = users.get(userId);
            Book book = userReadingBooks.get(userId);
            if (book != null) {
                user.addCreditScore(-10);
                moveInfos.add(new LibraryMoveInfo(book.getId(), "rr", "bs"));
                recordTraces(traces, book.getId(), date, LibraryBookState.READING_ROOM,
                        LibraryBookState.BOOKSHELF);
                bookShelf.addNormalBook(book);
            }
        }
        userReadingBooks.clear();
        return moveInfos;
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
