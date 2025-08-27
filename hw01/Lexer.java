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
            } else if (c == 'x') {
                tokens.add(new Token(Token.Type.VAL, "x"));
                pos++;
            } else if (c == '^') {
                tokens.add(new Token(Token.Type.POW, "^"));
                pos++;
            } else if (Character.isDigit(c)) {
                StringBuilder sb = new StringBuilder();
                while (pos < input.length() && Character.isDigit(input.charAt(pos))) {
                    sb.append(input.charAt(pos));
                    pos++;
                }
                tokens.add(new Token(Token.Type.NUM, sb.toString()));
            } else {
                pos++; // 跳过未知字符继续执行
                throw new IllegalArgumentException("Unrecognized character: " + input.charAt(pos));
            }
        }
    }

    public List<Token> getTokens() {
        return new ArrayList<>(tokens);
    }
}