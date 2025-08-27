import java.util.ArrayList;
import java.util.List;

public class Lexer {
    private final List<Token> tokens = new ArrayList<>();

    public Lexer(String input) {
        int pos = 0;
        while (pos < input.length()) {
            char c = input.charAt(pos);
            if (c == '(') {
                tokens.add(new Token(Token.Type.LPAREN, "("));
                pos++;
            } else if (c == ')') {
                tokens.add(new Token(Token.Type.RPAREN, ")"));
                pos++;
            } else if (c == '+') {
                tokens.add(new Token(Token.Type.ADD, "+"));
                pos++;
            } else if (c == '-') {
                tokens.add(new Token(Token.Type.SUB, "-"));
                pos++;
            } else if (c == '*') {
                tokens.add(new Token(Token.Type.MUL, "*"));
                pos++;
            } else if (c == '^') {
                tokens.add(new Token(Token.Type.POW, "^"));
                pos++;
            } else if (c == 'x') {
                tokens.add(new Token(Token.Type.VAL, "x"));
                pos++;
            } else if (c == 's') {
                tokens.add(new Token(Token.Type.SIN, "sin"));
                pos += 3;
            } else if (c == 'c') {
                tokens.add(new Token(Token.Type.COS, "cos"));
                pos += 3;
            } else if (c == ',') {
                tokens.add(new Token(Token.Type.COMMA, ","));
                pos++;
            } else if (c == '=') {
                tokens.add(new Token(Token.Type.EQ, "="));
                pos++;
            } else if (c == '{') {
                tokens.add(new Token(Token.Type.LBRACE, "{"));
                pos++;
            } else if (c == '}') {
                tokens.add(new Token(Token.Type.RBRACE, "}"));
                pos++;
            } else if (c == 'f') {
                tokens.add(new Token(Token.Type.FUNC, "f"));
                pos++;
            } else if (Character.isDigit(c)) {
                StringBuilder sb = new StringBuilder();
                while (pos < input.length() && Character.isDigit(input.charAt(pos))) {
                    sb.append(input.charAt(pos));
                    pos++;
                }
                tokens.add(new Token(Token.Type.NUM, sb.toString()));
            } else {
                pos++; // 跳过无效字符
            }
        }
    }

    public List<Token> getTokens() {
        return tokens;
    }
}