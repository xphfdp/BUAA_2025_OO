import java.util.Scanner;

public class MainClass {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        int numNorFunc = Integer.parseInt(scanner.nextLine().trim()); //读取普通函数个数
        for (int i = 0; i < numNorFunc; i++) {
            String norFunc = Pretreatment.pre(scanner.nextLine().trim());
            NorDefiner.addNorFunc(norFunc); // 添加普通函数定义
        }
        int numRecFunc = Integer.parseInt(scanner.nextLine().trim()); // 读取递推函数组数
        for (int i = 0; i < 3 * numRecFunc; i++) {
            String def = Pretreatment.pre(scanner.nextLine().trim());
            RecDefiner.addFunc(def); // 添加递推函数定义
        }
        String input = Pretreatment.pre(scanner.nextLine().trim()); // 读取待展开表达式
        System.out.println(input);
        Lexer lexer = new Lexer(input);
        Parser parser = new Parser(lexer.getTokens());
        Expression expr = parser.parseExpression();
        Poly result = expr.toPoly();
        System.out.println(Aftertreatment.addBrackets(result.toString()).replaceAll("-1\\*", "-"));
    }
}