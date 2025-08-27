public class Aftertreatment {
    public static String addBrackets(String expression) {
        return process(expression);
    }

    private static String process(String expr) {
        StringBuilder result = new StringBuilder();
        int i = 0;

        while (i < expr.length()) {
            if (i + 3 < expr.length() && (expr.startsWith("sin(", i)
                    || expr.startsWith("cos(", i))) {
                String func = expr.substring(i, i + 3);
                int start = i + 4; // position after '('
                int end = findMatchingParenthesis(expr, start - 1);

                if (end == -1) {
                    throw new RuntimeException("Unmatched parenthesis in expression!");
                }

                String innerExpr = expr.substring(start, end);
                String processedInner = process(innerExpr); // Recursive process inner expression

                // 判断是否需要加括号
                if (needsBrackets(innerExpr)) {
                    processedInner = "(" + processedInner + ")";
                }

                result.append(func).append("(").append(processedInner).append(")");

                i = end + 1; // Move index past the current processed part
            } else {
                result.append(expr.charAt(i));
                i++;
            }
        }

        return result.toString();
    }

    // 判断括号内是否需要额外括号
    private static boolean needsBrackets(String expr) {
        boolean hasOperator = false;
        boolean hasBracket = false;
        int bracketLevel = 0;

        for (char c : expr.toCharArray()) {
            if (c == '(') {
                hasBracket = true;
                bracketLevel++;
            } else if (c == ')') {
                bracketLevel--;
            } else if (bracketLevel == 0 && (c == '+' || c == '-' || c == '*')) {
                hasOperator = true;
            }
        }

        return (hasOperator && !hasBracket) || (hasOperator && hasBracket);
    }

    // 找到配对的右括号
    private static int findMatchingParenthesis(String s, int openPos) {
        int depth = 0;
        for (int i = openPos; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c == '(') {
                depth++;
            } else if (c == ')') {
                depth--;
                if (depth == 0) {
                    return i;
                }
            }
        }
        return -1; // 没有找到匹配括号
    }
}
