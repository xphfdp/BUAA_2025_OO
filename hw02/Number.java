import java.math.BigInteger;
import java.util.HashMap;

public class Number implements Factor {
    private BigInteger value;

    public Number(BigInteger value) {
        this.value = value;
    }

    public BigInteger getValue() {
        return value;
    }

    @Override
    public String toString() {
        return value.toString();
    }

    @Override
    public Poly toPoly() {
        return new Poly(new Mono(value, BigInteger.ZERO, new HashMap<>(), new HashMap<>()
        ));
    }
}