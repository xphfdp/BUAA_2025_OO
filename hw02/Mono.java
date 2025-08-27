import java.math.BigInteger;
import java.util.HashMap;

public class Mono {
    private BigInteger coe; // 系数
    private BigInteger exp; // 指数
    private HashMap<String, BigInteger> sinMap; //所有sin括号里的内容及其指数
    private HashMap<String, BigInteger> cosMap; //所有cos括号里的内容及其指数

    public Mono(BigInteger coe, BigInteger exp, HashMap<String, BigInteger> sinMap,
                HashMap<String, BigInteger> coeMap) {
        this.coe = coe;
        this.exp = exp;
        this.sinMap = sinMap;
        this.cosMap = coeMap;
    }

    public BigInteger getCoe() {
        return coe;
    }

    public BigInteger getExp() {
        return exp;
    }

    public HashMap<String, BigInteger> getSinMap() {
        return new HashMap<>(sinMap);
    }

    public HashMap<String, BigInteger> getCosMap() {
        return new HashMap<>(cosMap);
    }

    public Mono multiply(Mono other) {
        BigInteger newCoe = coe.multiply(other.coe);
        BigInteger newExp = exp.add(other.exp);
        HashMap<String, BigInteger> newSinMap = new HashMap<>(sinMap);
        HashMap<String, BigInteger> newCosMap = new HashMap<>(cosMap);
        // 合并 sinMap
        for (String key : other.sinMap.keySet()) {
            newSinMap.put(key, newSinMap.getOrDefault(key, BigInteger.ZERO)
                    .add(other.sinMap.get(key)));
        }
        // 合并 cosMap
        for (String key : other.cosMap.keySet()) {
            newCosMap.put(key, newCosMap.getOrDefault(key, BigInteger.ZERO)
                    .add(other.cosMap.get(key)));
        }
        return new Mono(newCoe, newExp, newSinMap, newCosMap);
    }

    public Mono normalize() {
        HashMap<String, BigInteger> normalizedSinMap = new HashMap<>(sinMap);
        normalizedSinMap.entrySet().removeIf(entry -> entry.getValue()
                .compareTo(BigInteger.ZERO) <= 0);
        HashMap<String, BigInteger> normalizedCosMap = new HashMap<>(cosMap);
        normalizedCosMap.entrySet().removeIf(entry -> entry.getValue()
                .compareTo(BigInteger.ZERO) <= 0);
        return new Mono(coe, exp, normalizedSinMap, normalizedCosMap);
    }

    @Override
    public String toString() {
        if (coe.equals(BigInteger.ZERO)) {
            return "0";
        }
        StringBuilder sb = new StringBuilder();
        // 处理系数
        if (!coe.equals(BigInteger.ONE) ||
                (exp.equals(BigInteger.ZERO) && sinMap.isEmpty() && cosMap.isEmpty())) {
            sb.append(coe);
        }
        // 处理 x 的指数
        if (exp.compareTo(BigInteger.ZERO) > 0) {
            if (sb.length() > 0) {
                sb.append("*");
            }
            sb.append("x");
            if (exp.compareTo(BigInteger.ONE) > 0) {
                sb.append("^").append(exp);
            }
        }
        // 处理 sin 项
        for (String key : sinMap.keySet()) {
            if (sb.length() > 0) {
                sb.append("*");
            }
            sb.append("sin(").append(key).append(")");
            if (sinMap.get(key).compareTo(BigInteger.ONE) > 0) {
                sb.append("^").append(sinMap.get(key));
            }
        }
        // 处理 cos 项
        for (String key : cosMap.keySet()) {
            if (sb.length() > 0) {
                sb.append("*");
            }
            sb.append("cos(").append(key).append(")");
            if (cosMap.get(key).compareTo(BigInteger.ONE) > 0) {
                sb.append("^").append(cosMap.get(key));
            }
        }
        return sb.toString();
    }
}