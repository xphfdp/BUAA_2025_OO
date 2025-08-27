import java.math.BigInteger;

public class Power implements Factor {
    private final int exponent;

    public Power(int exponent) {
        this.exponent = exponent;
    }

    @Override
    public Poly toPoly() {
        return new Poly().addTerm(exponent, BigInteger.ONE);
    }
}