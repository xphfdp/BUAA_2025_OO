import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

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

    @Override
    public Factor derive() {
        if (exponent == 0) {
            return new Number(BigInteger.ZERO); // 常数求导为 0
        } else if (exponent == 1) {
            return base.derive();
        } else {
            // 链式法则：n * base^(n-1) * base'
            Factor coeff = new Number(BigInteger.valueOf(exponent));
            Factor newBase = (exponent - 1 == 1) ? base : new Power(base, exponent - 1);
            Factor baseDerived = base.derive();
            List<Factor> factors = new ArrayList<>();
            factors.add(coeff);
            factors.add(newBase);
            factors.add(baseDerived);
            return new Term(factors);
        }
    }
}