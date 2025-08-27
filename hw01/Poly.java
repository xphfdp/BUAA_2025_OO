import java.math.BigInteger;
import java.util.Collections;
import java.util.Map;
import java.util.TreeMap;

public class Poly {
    private final Map<Integer, BigInteger> terms = new TreeMap<>(Collections.reverseOrder());

    public Poly addTerm(int exponent, BigInteger coefficient) {
        terms.merge(exponent, coefficient, BigInteger::add);
        return this;
    }

    public Poly add(Poly other) {
        Poly result = new Poly();
        result.terms.putAll(this.terms);
        for (Map.Entry<Integer, BigInteger> entry : other.terms.entrySet()) {
            result.addTerm(entry.getKey(), entry.getValue());
        }
        return result;
    }

    public Poly sub(Poly other) {
        Poly result = new Poly();
        result.terms.putAll(this.terms);
        for (Map.Entry<Integer, BigInteger> entry : other.terms.entrySet()) {
            result.addTerm(entry.getKey(), entry.getValue().negate());
        }
        return result;
    }

    public Poly mul(Poly other) {
        Poly result = new Poly();
        for (Map.Entry<Integer, BigInteger> term1 : this.terms.entrySet()) {
            for (Map.Entry<Integer, BigInteger> term2 : other.terms.entrySet()) {
                int newExponent = term1.getKey() + term2.getKey();
                BigInteger newCoefficient = term1.getValue().multiply(term2.getValue());
                result.addTerm(newExponent, newCoefficient);
            }
        }
        return result;
    }

    public Poly pow(int n) {
        int exponent = n;
        if (exponent < 0) {
            throw new IllegalArgumentException("Exponent must be non-negative");
        }
        Poly result = new Poly().addTerm(0, BigInteger.ONE); // 初始为1
        Poly base = this;
        while (exponent > 0) {
            if (exponent % 2 == 1) {
                result = result.mul(base);
            }
            base = base.mul(base);
            exponent /= 2;
        }
        return result;
    }

    @Override
    public String toString() {
        if (terms.isEmpty()) {
            return "0";
        }
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (Map.Entry<Integer, BigInteger> entry : terms.entrySet()) {
            BigInteger coeff = entry.getValue();
            if (coeff.compareTo(BigInteger.ZERO) == 0) {
                continue;
            }
            if (!first) {
                sb.append(coeff.signum() > 0 ? "+" : "-");
            } else if (coeff.signum() < 0) {
                sb.append("-");
            }
            first = false;
            BigInteger absCoeff = coeff.abs();
            int exp = entry.getKey();
            if (exp == 0) {
                sb.append(absCoeff);
            } else {
                if (!absCoeff.equals(BigInteger.ONE)) {
                    sb.append(absCoeff).append("*");
                }
                sb.append("x");
                if (exp > 1) {
                    sb.append("^").append(exp);
                }
            }
        }
        return sb.length() > 0 ? sb.toString() : "0";
    }
}