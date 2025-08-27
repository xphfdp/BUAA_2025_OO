import com.oocourse.library1.LibraryBookId;

import java.util.ArrayList;
import java.util.List;

public class BookShelf {
    private List<Book> books;

    public BookShelf() {
        this.books = new ArrayList<>();
    }

    public void addBook(Book book) {
        books.add(book);
    }

    public Book getBook(LibraryBookId bookId) {
        for (Book book : books) {
            if (book.getId().equals(bookId)) {
                return book;
            }
        }
        return null;
    }

    public void removeBook(Book book) {
        books.remove(book);
    }

    public List<Book> getBooks() {
        return books;
    }
}
