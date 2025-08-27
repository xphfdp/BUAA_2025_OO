import java.math.BigInteger;
import java.util.HashMap;
import java.util.List;

public class Expression implements Factor {
    private final List<Term> terms;
    private final List<String> ops;
    private int exponent = 1;

    public Expression(List<Term> terms, List<String> ops) {
        this.terms = terms;
        this.ops = ops;
    }

    public void setExponent(int exponent) {
        this.exponent = exponent;
    }

    @Override
    public Poly toPoly() {
        Poly result = new Poly();
        for (int i = 0; i < terms.size(); i++) {
            Poly termPoly = terms.get(i).toPoly();
            if (ops.get(i).equals("-")) {
                termPoly = termPoly.negate();
            }
            result = result.addPoly(termPoly);
        }
        // Apply the exponent to the entire expression
        Poly finalResult = new Poly(new Mono(
                java.math.BigInteger.ONE,
                BigInteger.ZERO,
                new HashMap<>(), // Empty sinMap
                new HashMap<>()  // Empty cosMap
        ));
        for (int i = 0; i < exponent; i++) {
            finalResult = finalResult.mulPoly(result);
        }
        return finalResult;
    }

    @Override
    public String toString() {
        return toPoly().toString();
    }
}