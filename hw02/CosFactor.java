import java.math.BigInteger;
import java.util.HashMap;

public class CosFactor implements Factor {
    private Factor factor;
    private BigInteger exponent;

    public CosFactor(Factor factor, BigInteger exponent) {
        this.factor = factor;
        this.exponent = exponent;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("cos(").append(factor.toString()).append(")");
        if (!exponent.equals(BigInteger.ONE)) {
            sb.append("^").append(exponent);
        }
        return sb.toString();
    }

    @Override
    public Poly toPoly() {
        // 将 cos 因子转换为单项式形式，保留 cos 的结构
        HashMap<String, BigInteger> cosMap = new HashMap<>();
        cosMap.put(factor.toString(), exponent);
        if (exponent.equals(BigInteger.ZERO)) {
            return new Poly(new Mono(BigInteger.ONE, BigInteger.ZERO,
                    new HashMap<>(), new HashMap<>()));
        }
        Poly innerPoly = factor.toPoly();
        if (innerPoly.isConstant()) {
            BigInteger value = innerPoly.getConstantValue();
            if (value.equals(BigInteger.ZERO)) {
                return new Poly(new Mono(BigInteger.ONE, BigInteger.ZERO,
                        new HashMap<>(), new HashMap<>()));
            }
        }
        return new Poly(new Mono(BigInteger.ONE, BigInteger.ZERO,
                new HashMap<String, BigInteger>(), cosMap));
    }
}
