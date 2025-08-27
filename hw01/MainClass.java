import java.util.List;
import java.util.Scanner;

public class MainClass {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        String input = Pretreatment.pre(scanner.nextLine());
        Lexer lexer = new Lexer(input);
        List<Token> tokens = lexer.getTokens();
        Parser parser = new Parser(tokens);
        Expression expr = parser.parseExpression();
        Poly poly = expr.toPoly();
        System.out.println(poly.toString());
        scanner.close();
    }
}