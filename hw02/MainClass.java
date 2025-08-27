import java.util.Scanner;

public class MainClass {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        int n = Integer.parseInt(scanner.nextLine().trim()); // 读取组数
        for (int i = 0; i < 3 * n; i++) {
            String def = Pretreatment.pre(scanner.nextLine().trim());
            Definer.addFunc(def); // 添加函数定义
        }
        String input = Pretreatment.pre(scanner.nextLine().trim()); // 读取待展开表达式
        Lexer lexer = new Lexer(input);
        Parser parser = new Parser(lexer.getTokens());
        Expression expr = parser.parseExpression();
        Poly result = expr.toPoly();
        System.out.println(Aftertreatment.addBrackets(result.toString()).replaceAll("-1\\*","-"));
    }
}