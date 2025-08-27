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
        if (peek() != null && (peek().getType() == Token.Type.ADD ||
                peek().getType() == Token.Type.SUB)) {
            ops.add(peek().getType() == Token.Type.ADD ? "+" : "-");
            pos++;
        } else {
            ops.add("+");
        }
        terms.add(parseTerm());
        while (peek() != null && (peek().getType() == Token.Type.ADD ||
                peek().getType() == Token.Type.SUB)) {
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
            pos++;
            factors.add(parseFactor());
        }
        return new Term(factors);
    }

    public Factor parseFactor() {
        Token token = peek();
        if (token == null) {
            throw new RuntimeException("Unexpected end of input");
        }
        Factor factor;
        if (token.getType() == Token.Type.NUM) {
            String numStr = expect(Token.Type.NUM).getContent();
            factor = new Number(new BigInteger(numStr));
        } else if (token.getType() == Token.Type.VAL) {
            expect(Token.Type.VAL);
            factor = new Var();
        } else if (token.getType() == Token.Type.LPAREN) {
            expect(Token.Type.LPAREN);
            Expression expr = parseExpression();
            expect(Token.Type.RPAREN);
            factor = expr;
        } else if (token.getType() == Token.Type.SIN) {
            pos++;
            factor = parseSinCosFactor("sin");
        } else if (token.getType() == Token.Type.COS) {
            pos++;
            factor = parseSinCosFactor("cos");
        } else if (token.getType() == Token.Type.RECFUNC) {
            pos++; // Skip 'f'
            factor = parseRecFuncFactor();
        } else if (token.getType() == Token.Type.NORFUNC) {
            String name = token.getContent(); //函数名g/h
            pos++; // Skip 'g' or 'h'
            expect(Token.Type.LPAREN);
            ArrayList<Factor> actualParams = new ArrayList<>();
            String finalName = name;
            if (peek() != null && peek().getType() != Token.Type.RPAREN) {
                actualParams.add(parseExpression());
                while (peek() != null && peek().getType() == Token.Type.COMMA) {
                    pos++; // Skip comma
                    actualParams.add(parseExpression());
                }
            }
            expect(Token.Type.RPAREN);
            factor = new NorFuncFactor(finalName, actualParams);
        } else if (token.getType() == Token.Type.DX) {
            pos++; //skip 'dx'
            factor = parseDeriveFactor();
        } else {
            throw new RuntimeException("Unexpected token: " + token.getContent());
        }
        // 处理指数
        if (peek() != null && peek().getType() == Token.Type.POW) {
            expect(Token.Type.POW);
            Token expToken = expect(Token.Type.NUM);
            int exponent = Integer.parseInt(expToken.getContent());
            if (factor instanceof Expression) {
                ((Expression) factor).setExponent(exponent);
                return factor;
            } else {
                return new Power(factor, exponent);
            }
        }
        return factor;
    }

    private Factor parseDeriveFactor() {
        expect(Token.Type.LPAREN);
        Expression expr = parseExpression();
        expect(Token.Type.RPAREN);
        return expr.derive();
    }

    private Factor parseRecFuncFactor() {
        expect(Token.Type.LBRACE);
        Token indexToken = expect(Token.Type.NUM);
        expect(Token.Type.RBRACE);
        expect(Token.Type.LPAREN);
        ArrayList<Factor> actualParams = new ArrayList<>();
        String index = String.valueOf(indexToken.getContent());
        if (peek() != null && peek().getType() != Token.Type.RPAREN) {
            actualParams.add(parseExpression());
            while (peek() != null && peek().getType() == Token.Type.COMMA) {
                pos++; // Skip comma
                actualParams.add(parseExpression());
            }
        }
        expect(Token.Type.RPAREN);
        return new RecFuncFactor(index, actualParams);
    }

    private Factor parseSinCosFactor(String type) {
        expect(Token.Type.LPAREN);
        Factor inside = parseExpression();
        expect(Token.Type.RPAREN);
        BigInteger exponent = BigInteger.ONE;
        if (peek() != null && peek().getType() == Token.Type.POW) {
            expect(Token.Type.POW);
            exponent = BigInteger.valueOf(Integer.parseInt(expect(Token.Type.NUM).getContent()));
        }
        if (type.equals("sin")) {
            return new SinFactor(inside, exponent);
        } else {
            return new CosFactor(inside, exponent);
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
        throw new RuntimeException("Expected " + type +
                ", but found " + (token != null ? token.getContent() : "EOF"));
    }
}