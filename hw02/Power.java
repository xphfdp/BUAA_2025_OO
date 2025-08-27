import java.math.BigInteger;
import java.util.HashMap;

public class Power implements Factor {
    private final Factor base;
    private final int exponent;

    public Power(Factor base, int exponent) {
        this.base = base;
        this.exponent = exponent;
    }

    @Override
    public Poly toPoly() {
        Poly basePoly = base.toPoly();
        Poly result = new Poly(new Mono(BigInteger.ONE, BigInteger.ZERO,
                new HashMap<>(), new HashMap<>()));
        for (int i = 0; i < exponent; i++) {
            result = result.mulPoly(basePoly);
        }
        return result;
    }

    @Override
    public String toString() {
        return base.toString() + "^" + exponent;
    }
}