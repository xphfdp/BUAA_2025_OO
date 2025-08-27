import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Lexer {
    private final List<Token> tokens = new ArrayList<>();

    public Lexer(String input) {
        int pos = 0;
        while (pos < input.length()) {
            char c = input.charAt(pos);
            String[] singleTokens = {"(", ")", "+", "-", "*", "^", "x",
                ",", "=", "{", "}", "f", "g", "h"};
            Token.Type[] singleTypes = {Token.Type.LPAREN, Token.Type.RPAREN, Token.Type.ADD,
                Token.Type.SUB,
                Token.Type.MUL, Token.Type.POW, Token.Type.VAL, Token.Type.COMMA, Token.Type.EQ,
                Token.Type.LBRACE, Token.Type.RBRACE, Token.Type.RECFUNC, Token.Type.NORFUNC,
                Token.Type.NORFUNC};

            // 处理单字符token
            int singleIndex = Arrays.asList(singleTokens).indexOf(String.valueOf(c));
            if (singleIndex != -1) {
                tokens.add(new Token(singleTypes[singleIndex], singleTokens[singleIndex]));
                pos++;
            }
            // 处理多字符token
            else if (pos + 2 < input.length() && input.substring(pos, pos + 3).matches("sin|cos")) {
                String val = input.substring(pos, pos + 3);
                tokens.add(new Token(val.equals("sin") ? Token.Type.SIN : Token.Type.COS, val));
                pos += 3;
            }
            else if (pos + 1 < input.length() && input.substring(pos, pos + 2).equals("dx")) {
                tokens.add(new Token(Token.Type.DX, "dx"));
                pos += 2;
            }
            // 处理数字
            else if (Character.isDigit(c)) {
                StringBuilder sb = new StringBuilder();
                while (pos < input.length() && Character.isDigit(input.charAt(pos))) {
                    sb.append(input.charAt(pos++));
                }
                tokens.add(new Token(Token.Type.NUM, sb.toString()));
            }
            else {
                pos++; // 跳过无效字符
            }
        }
    }

    public List<Token> getTokens() {
        return tokens;
    }
}