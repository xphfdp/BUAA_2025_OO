import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;

public class Poly {
    private ArrayList<Mono> monoList;

    public Poly() {
        monoList = new ArrayList<>();
    }

    public Poly(Mono mono) {
        monoList = new ArrayList<>();
        monoList.add(mono);
    }

    public Poly addPoly(Poly other) {
        Poly result = new Poly();
        result.monoList.addAll(this.monoList);
        result.monoList.addAll(other.monoList);
        // 合并同类项
        result.simplify();
        return result;
    }

    public Poly mulPoly(Poly other) {
        Poly result = new Poly();
        for (Mono m1 : this.monoList) {
            for (Mono m2 : other.monoList) {
                result.monoList.add(m1.multiply(m2));
            }
        }
        result.simplify();
        return result;
    }

    public Poly negate() {
        Poly result = new Poly();
        for (Mono m : monoList) {
            result.monoList.add(new Mono(m.getCoe().negate(),
                    m.getExp(), m.getSinMap(), m.getCosMap()));
        }
        return result;
    }

    private void simplify() {
        HashMap<String, Mono> map = new HashMap<>();
        for (Mono m : monoList) {
            Mono normalized = m.normalize();
            String key = normalized.getExp() + "_" + normalized.getSinMap().toString()
                    + "_" + normalized.getCosMap().toString();
            if (map.containsKey(key)) {
                Mono existing = map.get(key);
                BigInteger newCoe = existing.getCoe().add(m.getCoe());
                map.put(key, new Mono(newCoe, normalized.getExp(),
                        normalized.getSinMap(), normalized.getCosMap()));
            } else {
                map.put(key, normalized);
            }
        }
        monoList.clear();
        monoList.addAll(map.values());
        monoList.removeIf(m -> m.getCoe().equals(BigInteger.ZERO));
    }

    public boolean isConstant() {
        if (monoList.isEmpty()) {
            return true; // 空多项式表示0，是常数
        }
        return monoList.size() == 1 && monoList.get(0).getExp().equals(BigInteger.ZERO) &&
                monoList.get(0).getSinMap().isEmpty() && monoList.get(0).getCosMap().isEmpty();
    }

    public BigInteger getConstantValue() {
        if (monoList.isEmpty()) {
            return BigInteger.ZERO;
        }
        if (!isConstant()) {
            throw new UnsupportedOperationException("Not a constant");
        }
        return monoList.get(0).getCoe();
    }

    @Override
    public String toString() {
        if (monoList.isEmpty()) {
            return "0";
        }
        StringBuilder sb = new StringBuilder();
        boolean first = true;

        for (Mono mono : monoList) {
            if (mono.getCoe().equals(BigInteger.ZERO)) {
                continue;
            }
            String monoStr = mono.toString();
            if (first) {
                sb.append(monoStr);
                first = false;
            } else {
                if (mono.getCoe().compareTo(BigInteger.ZERO) >= 0) {
                    sb.append("+").append(monoStr);
                } else {
                    sb.append(monoStr); // 负系数已包含在 monoStr 中
                }
            }
        }

        return sb.length() == 0 ? "0" : sb.toString();
    }
}