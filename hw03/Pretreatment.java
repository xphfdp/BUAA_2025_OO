import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Pretreatment {
    private String input;

    public Pretreatment(String input) {
        this.input = input;
    }

    //整合预处理
    public static String pre(String input) {
        return parenNeg(indexEqualOne(removePos(removeLead0(simpPosNeg(removeBlank(input))))));
    }

    //去除空白项
    private static String removeBlank(String str) {
        return str.replace(" ", "").replace("\t", "");
    }

    //去除前导零
    private static String removeLead0(String input) {
        // 第一步：处理有非零尾数的前导零（如 +0023 → +23）
        String step1 = input.replaceAll(
                "(?<![0-9x)])" +        // 确保前导零不在数字、x或)之后
                        "([+-]?)" +             // 捕获符号（可选）
                        "0+([1-9]\\d*)",       // 捕获前导零后的有效数字
                "$1$2"
        );

        return step1.replaceAll(
                "(?<![0-9x)])" +        // 同第一步的边界限制
                        "([+-]?)0+",           // 捕获符号和纯零
                "$10"                   // 保留符号并替换为单个零
        );
    }

    //使用正则表达式化简连续的正负号（有可能连续两个，也有可能连续三个）
    private static String simpPosNeg(String input) {
        Pattern pattern = Pattern.compile("[+-]+");
        Matcher matcher = pattern.matcher(input);
        StringBuffer sb = new StringBuffer();

        while (matcher.find()) {
            String group = matcher.group();
            String replacement = calculateReplacement(group);
            matcher.appendReplacement(sb, replacement);
        }
        matcher.appendTail(sb);
        String result = sb.toString();
        if (result.charAt(0) == '+') {
            result = result.substring(1);
        }
        return result.replaceAll("\\(\\+", "(");
    }

    private static String calculateReplacement(String operatorGroup) {
        int minusCount = 0;
        for (char c : operatorGroup.toCharArray()) {
            if (c == '-') {
                minusCount++;
            }
        }
        return (minusCount % 2 == 1) ? "-" : "+";
    }

    //去除'^'和'*'后的正号
    private static String removePos(String input) {
        int pos = 0;
        StringBuilder sb = new StringBuilder();
        while (pos < input.length()) {
            if ((input.charAt(pos) == '^' || input.charAt(pos) == '*')
                    && pos + 1 < input.length() && input.charAt(pos + 1) == '+') {
                sb.append(input.charAt(pos));
                pos += 2;
            } else {
                sb.append(input.charAt(pos));
                pos++;
            }
        }

        return sb.toString();
    }

    //化简指数为1的项
    private static String indexEqualOne(String input) {
        int pos = 0;
        StringBuilder sb = new StringBuilder();
        while (pos < input.length()) {
            if (input.charAt(pos) == '^') {
                if (pos + 1 < input.length() && input.charAt(pos + 1) == '1'
                        && pos + 2 < input.length() && !Character.isDigit(input.charAt(pos + 2))) {
                    pos += 2;
                } else {
                    sb.append(input.charAt(pos));
                    pos++;
                }
            } else {
                sb.append(input.charAt(pos));
                pos++;
            }
        }

        return sb.toString();
    }

    //处理'*'紧接'-'的情况，解决方法是用括号将负项括起来
    private static String parenNeg(String input) {
        int pos = 0;
        StringBuilder sb = new StringBuilder();
        while (pos < input.length()) {
            if (pos + 1 < input.length() &&
                    input.charAt(pos) == '*' && input.charAt(pos + 1) == '-') {
                sb.append("*(");
                sb.append("-");
                pos += 2;
                while (pos < input.length() && !isOperator(input.charAt(pos))) {
                    sb.append(input.charAt(pos));
                    pos++;
                }
                sb.append(")");
            } else {
                sb.append(input.charAt(pos));
                pos++;
            }
        }
        return sb.toString();
    }

    private static boolean isOperator(char c) {
        return c == '+' || c == '-' || c == '*';
    }
}
