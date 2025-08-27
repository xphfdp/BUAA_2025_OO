import java.util.ArrayList;

public class NorFuncFactor implements Factor {
    private String newNorFunc;
    private Expression norExpr;

    public NorFuncFactor(String name, ArrayList<Factor> actualParas) {
        this.newNorFunc = NorDefiner.callNorFunc(name.charAt(0), actualParas);
        this.norExpr = setNorExpr();
    }

    private Expression setNorExpr() {
        String str = Pretreatment.pre(newNorFunc);
        Lexer lexer = new Lexer(str);
        Parser parser = new Parser(lexer.getTokens());
        return parser.parseExpression();
    }

    @Override
    public String toString() {
        return norExpr.toString();
    }

    @Override
    public Poly toPoly() {
        return norExpr.toPoly();
    }

    @Override
    public Factor derive() {
        return norExpr.derive();
    }
}
