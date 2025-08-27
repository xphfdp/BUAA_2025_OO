import com.oocourse.library3.LibraryBookId;
import com.oocourse.library3.LibraryBookIsbn;

import java.util.HashSet;

import static java.lang.Math.max;
import static java.lang.Math.min;

public class User {
    private String id;
    private HashSet<Book> books;
    private int creditScore;

    public User(String id) {
        this.id = id;
        this.books = new HashSet<>();
        this.creditScore = 100;
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

    public void addCreditScore(int score) {
        if (score >= 0) {
            this.creditScore  = min(this.creditScore + score, 180);
        } else {
            this.creditScore = max(this.creditScore + score, 0);
        }
    }

    public int getCreditScore() {
        return creditScore;
    }

    public HashSet<Book> getHeldBooks() {
        return books;
    }

    public void orderNewBook() {

    }
}
