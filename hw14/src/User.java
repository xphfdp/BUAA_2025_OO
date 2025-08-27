import com.oocourse.library2.LibraryBookId;
import com.oocourse.library2.LibraryBookIsbn;

import java.util.HashSet;

public class User {
    private String id;
    private HashSet<Book> books;

    public User(String id) {
        this.id = id;
        this.books = new HashSet<>();
    }

    public void addBook(Book book) {
        books.add(book);
    }

    public void removeBook(Book book) {
        books.remove(book);
    }

    public boolean haveBookB() {
        for (Book book : books) {
            if (book.isTypeB()) {
                return true;
            }
        }
        return false;
    }

    public boolean haveCertainBook(LibraryBookIsbn bookIsbn) {
        for (Book book : books) {
            if (book.getId().getBookIsbn().equals(bookIsbn.getBookIsbn())) {
                return true;
            }
        }
        return false;
    }

    public Book getBook(LibraryBookId bookId) {
        for (Book book : books) {
            if (book.getId().equals(bookId)) {
                return book;
            }
        }
        return null;
    }

    public boolean canBorrowOrOrder(LibraryBookIsbn bookId) {
        if (bookId.isTypeA()) {
            return false;
        } else if (bookId.isTypeB()) {
            return !haveBookB();
        } else if (bookId.isTypeC()) {
            return !haveCertainBook(bookId);
        }
        return false;
    }
}
