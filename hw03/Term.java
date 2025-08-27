import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

public class Term implements Factor {
    private final List<Factor> factors;

    public Term(List<Factor> factors) {
        this.factors = factors;
    }

    @Override
    public Poly toPoly() {
        Poly result = new Poly(new Mono(java.math.BigInteger.ONE,
                BigInteger.ZERO, new HashMap<>(), new HashMap<>()));
        for (Factor factor : factors) {
            result = result.mulPoly(factor.toPoly());
        }
        return result;
    }

    @Override
    public String toString() {
        return factors.toString();
    }

    public Term derive() {
        if (factors.size() == 1) {
            return new Term(Collections.singletonList(factors.get(0).derive()));
        }
        // 乘法法则：f' * g + f * g'
        List<Term> derivedTerms = new ArrayList<>();
        for (int i = 0; i < factors.size(); i++) {
            List<Factor> newFactors = new ArrayList<>();
            for (int j = 0; j < factors.size(); j++) {
                if (i == j) {
                    newFactors.add(factors.get(j).derive());
                } else {
                    newFactors.add(factors.get(j));
                }
            }
            derivedTerms.add(new Term(newFactors));
        }
        List<String> ops = new ArrayList<>(Collections.nCopies(derivedTerms.size(), "+"));
        return new Expression(derivedTerms, ops).toTerm();
    }

    public Expression toExpression() {
        List<Term> terms = new ArrayList<>();
        terms.add(this);
        List<String> ops = new ArrayList<>();
        ops.add("+");
        return new Expression(terms, ops);
    }
}