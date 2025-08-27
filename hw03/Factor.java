public interface Factor {
    Poly toPoly();

    String toString();

    Factor derive();
}