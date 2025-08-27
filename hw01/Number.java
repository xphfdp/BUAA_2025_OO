import java.math.BigInteger;

public class Number implements Factor {
    private final BigInteger value;

    public Number(BigInteger value) {
        this.value = value;
    }

    @Override
    public Poly toPoly() {
        return new Poly().addTerm(0, value);
    }
}