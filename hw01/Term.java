import java.math.BigInteger;
import java.util.List;

public class Term {
    private final List<Factor> factors;

    public Term(List<Factor> factors) {
        this.factors = factors;
    }

    public Poly toPoly() {
        Poly result = new Poly().addTerm(0, BigInteger.ONE); // 初始为1
        for (Factor factor : factors) {
            result = result.mul(factor.toPoly());
        }
        return result;
    }
}