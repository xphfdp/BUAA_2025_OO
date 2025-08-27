import java.math.BigInteger;
import java.util.HashMap;

public class SinFactor implements Factor {
    private Factor factor;
    private BigInteger exponent;

    public SinFactor(Factor factor, BigInteger exponent) {
        this.factor = factor;
        this.exponent = exponent;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("sin(").append(factor.toString()).append(")");
        if (!exponent.equals(BigInteger.ONE)) {
            sb.append("^").append(exponent);
        }
        return sb.toString();
    }

    @Override
    public Poly toPoly() {
        // 将 sin 因子转换为单项式形式，保留 sin 的结构
        HashMap<String, BigInteger> sinMap = new HashMap<>();
        sinMap.put(factor.toString(), exponent);
        if (exponent.equals(BigInteger.ZERO)) {
            return new Poly(new Mono(BigInteger.ONE, BigInteger.ZERO,
                    new HashMap<>(), new HashMap<>()));
        }
        Poly innerPoly = factor.toPoly();
        if (innerPoly.isConstant()) {
            BigInteger value = innerPoly.getConstantValue();
            if (value.equals(BigInteger.ZERO)) {
                if (exponent.compareTo(BigInteger.ZERO) > 0) {
                    return new Poly(); // 返回空Poly，表示0
                } else {
                    return new Poly(new Mono(BigInteger.ONE, BigInteger.ZERO,
                            new HashMap<>(), new HashMap<>()));
                }
            }
        }
        return new Poly(new Mono(BigInteger.ONE,
                BigInteger.ZERO, sinMap, new HashMap<String, BigInteger>()));
    }
}
