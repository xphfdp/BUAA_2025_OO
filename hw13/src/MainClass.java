public class MainClass {
    public static void main(String[] args) {
        BookShelf bookShelf = new BookShelf();
        AppointmentOffice appointmentOffice = new AppointmentOffice(bookShelf);
        BorrowReturnOffice borrowOffice = new BorrowReturnOffice(bookShelf);
        Library library = new Library(bookShelf, appointmentOffice, borrowOffice);
        library.run();
    }
}
