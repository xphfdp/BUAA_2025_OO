import java.util.ArrayList;

public class RecFuncFactor implements Factor {
    private String newFunc; // 将函数实参带入形参位置后的结果(字符串形式)
    private Expression expr; // 将 newFunc 解析成表达式后的结果

    public RecFuncFactor(String index, ArrayList<Factor> actualParas) {
        this.newFunc = RecDefiner.callFunc(index.charAt(0), actualParas); // 获取形参替换为实参后的表达式
        this.expr = setExpr(); // 对函数表达式进行解析
    }

    private Expression setExpr() {
        String s = Pretreatment.pre(newFunc); // 对字符串进行预处理
        Lexer lexer = new Lexer(s); // 词法解析
        Parser parser = new Parser(lexer.getTokens()); // 语法解析
        return parser.parseExpression();
    }

    @Override
    public String toString() {
        return expr.toString(); // 返回表达式的字符串形式
    }

    @Override
    public Poly toPoly() {
        return expr.toPoly(); // 返回表达式的多项式形式
    }

    @Override
    public Factor derive() {
        return expr.derive();
    }
}