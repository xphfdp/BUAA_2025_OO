import java.math.BigInteger;
import java.util.List;
import java.util.HashMap;

public class Term {
    private final List<Factor> factors;

    public Term(List<Factor> factors) {
        this.factors = factors;
    }

    public Poly toPoly() {
        Poly result = new Poly(new Mono(java.math.BigInteger.ONE,
                BigInteger.ZERO,new HashMap<>(),new HashMap<>()));
        for (Factor factor : factors) {
            result = result.mulPoly(factor.toPoly());
        }
        return result;
    }
}