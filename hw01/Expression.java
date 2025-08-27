import java.util.List;

public class Expression {
    private final List<Term> terms;
    private final List<String> ops;

    public Expression(List<Term> terms, List<String> ops) {
        this.terms = terms;
        this.ops = ops;
    }

    public Poly toPoly() {
        Poly result = new Poly();
        for (int i = 0; i < terms.size(); i++) {
            Poly termPoly = terms.get(i).toPoly();
            if (ops.get(i).equals("+")) {
                result = result.add(termPoly);
            } else {
                result = result.sub(termPoly);
            }
        }
        return result;
    }
}