import com.oocourse.library2.LibraryBookState;
import com.oocourse.library2.LibraryBookIsbn;
import com.oocourse.library2.LibraryBookId;
import com.oocourse.library2.LibraryMoveInfo;
import com.oocourse.library2.LibraryTrace;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

public class BookShelf {
    private List<Book> hotBooks; // 热门书籍
    private List<Book> normalBooks; // 普通书籍

    public BookShelf() {
        this.hotBooks = new ArrayList<>();
        this.normalBooks = new ArrayList<>();
    }

    public void addHotBook(Book book) {
        hotBooks.add(book);
    }

    public void addNormalBook(Book book) {
        normalBooks.add(book);
    }

    public List<Book> getBooks() {
        List<Book> allBooks = new ArrayList<>();
        allBooks.addAll(hotBooks);
        allBooks.addAll(normalBooks);
        return allBooks;
    }

    public void removeBook(Book book) {
        if (hotBooks.contains(book)) {
            hotBooks.remove(book);
        } else if (normalBooks.contains(book)) {
            normalBooks.remove(book);
        }
    }

    public boolean isHotBook(Book book) {
        return hotBooks.contains(book);
    }

    /**
     * 整理书架
     * 满足：热门书架上只有热门书籍，普通书架上只有普通书籍
     */
    public List<LibraryMoveInfo> sortBooks(Map<LibraryBookId,
            List<LibraryTrace>> traces, LocalDate date, HashSet<LibraryBookIsbn> todayHotBooks) {
        List<LibraryMoveInfo> moveInfos = new ArrayList<>();
        List<Book> hotBooksToRemove = new ArrayList<>();
        List<Book> normalBooksToRemove = new ArrayList<>();
        for (Book book : normalBooks) {
            if (todayHotBooks.contains(book.getId().getBookIsbn())) {
                // 普通书架上成为热门书籍的书籍
                normalBooksToRemove.add(book);
                moveInfos.add(new LibraryMoveInfo(book.getId(), "bs", "hbs"));
                recordTraces(traces, book.getId(), date, LibraryBookState.BOOKSHELF,
                        LibraryBookState.HOT_BOOKSHELF);
            } else {
                continue;
            }
        }
        for (Book book : hotBooks) {
            if (todayHotBooks.contains(book.getId().getBookIsbn())) {
                continue;
            } else {
                // 热门书架上不再是热门书籍的书籍
                hotBooksToRemove.add(book);
                moveInfos.add(new LibraryMoveInfo(book.getId(), "hbs", "bs"));
                recordTraces(traces, book.getId(), date, LibraryBookState.HOT_BOOKSHELF,
                        LibraryBookState.BOOKSHELF);
            }
        }
        hotBooks.removeAll(hotBooksToRemove);
        normalBooks.removeAll(normalBooksToRemove);
        hotBooks.addAll(normalBooksToRemove);
        normalBooks.addAll(hotBooksToRemove);
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
