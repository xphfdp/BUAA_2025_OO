public class SubExpression implements Factor {
    private final Expression expr;
    private final int exponent;

    public SubExpression(Expression expr, int exponent) {
        this.expr = expr;
        this.exponent = exponent;
    }

    @Override
    public Poly toPoly() {
        Poly poly = expr.toPoly();
        return poly.pow(exponent);
    }
}