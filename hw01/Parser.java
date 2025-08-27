import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

public class Parser {
    private final List<Token> tokens;
    private int pos;

    public Parser(List<Token> tokens) {
        this.tokens = tokens;
        this.pos = 0;
    }

    public Expression parseExpression() {
        List<Term> terms = new ArrayList<>();
        List<String> ops = new ArrayList<>();
        // 处理开头的正负号
        if (peek() != null &&
                (peek().getType() == Token.Type.ADD || peek().getType() == Token.Type.SUB)) {
            ops.add(peek().getType() == Token.Type.ADD ? "+" : "-");
            pos++;
        } else {
            ops.add("+"); // 默认正号
        }
        terms.add(parseTerm());
        while (peek() != null &&
                (peek().getType() == Token.Type.ADD || peek().getType() == Token.Type.SUB)) {
            ops.add(peek().getContent());
            pos++;
            terms.add(parseTerm());
        }
        return new Expression(terms, ops);
    }

    private Term parseTerm() {
        List<Factor> factors = new ArrayList<>();
        factors.add(parseFactor());
        while (peek() != null && peek().getType() == Token.Type.MUL) {
            pos++; // 跳过 '*'
            factors.add(parseFactor());
        }
        return new Term(factors);
    }

    private Factor parseFactor() {
        Token token = peek();
        if (token == null) {
            throw new RuntimeException("Unexpected end of input");
        }
        if (token.getType() == Token.Type.NUM) {
            pos++;
            BigInteger number = new BigInteger(token.getContent());

            // 检查是否有幂运算符
            if (peek() != null && peek().getType() == Token.Type.POW) {
                pos++; // 跳过 '^'
                Token expToken = expect(Token.Type.NUM); // 期望指数为数字
                int exponent = Integer.parseInt(expToken.getContent());
                BigInteger value;
                if (exponent == 0 && number.equals(BigInteger.ZERO)) {
                    value = BigInteger.ONE;
                } else {
                    value = number.pow(exponent);
                }
                return new Number(value);
            } else {
                return new Number(number); // 无幂运算，返回普通 Number
            }
        } else if (token.getType() == Token.Type.VAL) {
            pos++;
            if (peek() != null && peek().getType() == Token.Type.POW) { // 检查 '^'
                pos++; // 跳过 '^'
                Token expToken = expect(Token.Type.NUM); // 获取指数
                int exponent = Integer.parseInt(expToken.getContent());
                return new Power(exponent); // 返回 x^exponent
            } else {
                return new Power(1); // 默认 x^1
            }
        } else if (token.getType() == Token.Type.LPAREN) {
            pos++; // 跳过 '('
            Expression expr = parseExpression();
            expect(Token.Type.RPAREN); // 匹配 ')'
            if (peek() != null && peek().getType() == Token.Type.POW) {
                pos++; // 跳过 '^'
                Token expToken = expect(Token.Type.NUM);
                int exponent = Integer.parseInt(expToken.getContent());
                return new SubExpression(expr, exponent);
            }
            return new SubExpression(expr, 1);
        } else {
            throw new RuntimeException("Unexpected token: " + token.getContent());
        }
    }

    private Token peek() {
        return pos < tokens.size() ? tokens.get(pos) : null;
    }

    private Token expect(Token.Type type) {
        Token token = peek();
        if (token != null && token.getType() == type) {
            pos++;
            return token;
        }
        throw new RuntimeException("Expected " + type
                + ", but found " + (token != null ? token.getContent() : "EOF"));
    }
}