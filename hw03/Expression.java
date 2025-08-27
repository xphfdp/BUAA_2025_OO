import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
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

    public Expression derived() {
        List<Term> derivedTerms = new ArrayList<>();
        List<String> opsCopy = new ArrayList<>(ops);
        for (Term term : terms) {
            Term derivedTerm = term.derive();
            derivedTerms.add(derivedTerm);
        }
        Expression derivedExpr = new Expression(derivedTerms, opsCopy);
        // 如果有指数，使用链式法则
        if (exponent > 1) {
            Factor coeff = new Number(BigInteger.valueOf(exponent));
            Expression base = new Expression(new ArrayList<>(terms), new ArrayList<>(ops));
            base.setExponent(exponent - 1);
            List<Factor> factors = new ArrayList<>();
            factors.add(coeff);
            factors.add(base);
            factors.add(derivedExpr);
            return new Term(factors).toExpression();
        }
        return derivedExpr;
    }

    @Override
    public Factor derive() {
        // 计算不考虑自身指数的导数
        if (exponent == 0) {
            return new Number(BigInteger.ZERO);
        }
        List<Term> derivedTerms = new ArrayList<>();
        for (Term term : terms) {
            derivedTerms.add(term.derive());
        }
        Factor innerDerivedExpr = new Expression(derivedTerms, ops);

        // 如果有指数大于1，应用链式法则：n * (expression)^(n-1) * innerDerivedExpr
        if (exponent > 1) {
            Factor coeff = new Number(BigInteger.valueOf(exponent));
            // 创建一个新表达式，保持原有的terms和ops，但指数减1
            Expression baseExpr = new Expression(new ArrayList<>(terms), new ArrayList<>(ops));
            baseExpr.setExponent(exponent - 1);
            // 导数为 coeff * baseExpr * innerDerivedExpr
            List<Factor> factors = new ArrayList<>();
            factors.add(coeff);
            factors.add(baseExpr);
            factors.add(innerDerivedExpr);
            return new Term(factors);
        } else {
            // 如果指数为1或小于1，直接返回内层导数
            return innerDerivedExpr;
        }
    }

    public Term toTerm() {
        if (terms.size() == 1 && ops.get(0).equals("+")) {
            return terms.get(0);
        }
        return new Term(Collections.singletonList(this));
    }
}