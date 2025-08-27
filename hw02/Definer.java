import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Definer {
    private static HashMap<Character, String> funcMap = new HashMap<>(); // key存储序号，value为定义式
    private static HashMap<Character, ArrayList<String>> paramMap = new HashMap<>();

    public static void addFunc(String input) {
        // 使用正则表达式匹配 f{序号}(形参)=定义式
        Pattern pattern = Pattern.compile("f\\{(\\w+)\\}\\((.*?)\\)=(.+)");
        Matcher matcher = pattern.matcher(input.trim());
        if (matcher.find()) {
            String index = matcher.group(1); // 提取序号
            String params = matcher.group(2); // 提取形参
            String definition = matcher.group(3).trim(); // 提取定义式

            // 存储定义式到 funcMap
            funcMap.put(index.charAt(0), definition);

            // 解析形参列表并存储到 paramMap
            ArrayList<String> paramList = new ArrayList<>();
            for (String param : params.split(",")) {
                paramList.add(param.trim());
            }
            paramMap.put(index.charAt(0), paramList);
        } else {
            throw new RuntimeException("Invalid function definition: " + input);
        }
    }

    public static String callFunc(Character funcKey, ArrayList<Factor> params) {
        String template;
        ArrayList<String> placeholders;

        if (funcKey.equals('0') || funcKey.equals('1')) {
            template = funcMap.get(funcKey);
            placeholders = paramMap.get(funcKey);
        } else {
            template = funcMap.get('n');
            char prior = (char) (funcKey - 1);
            char priorTwo = (char) (funcKey - 2);
            template = template.replace("n-1", String.valueOf(prior))
                    .replace("n-2", String.valueOf(priorTwo));
            placeholders = paramMap.get('0');
        }

        StringBuilder result = new StringBuilder(template);
        int paramCount = Math.min(placeholders.size(), params.size());

        for (int i = 0; i < paramCount; i++) {
            String placeholder = placeholders.get(i);
            String value = params.get(i).toPoly().toString();

            if ((funcKey.equals('0') || funcKey.equals('1')) && i == 0) {
                value = value.replace("x", "z");
            } else {
                value = value.replace("x", "z");
            }

            int startIndex = result.indexOf(placeholder);
            while (startIndex != -1) {
                int endIndex = startIndex + placeholder.length();
                result.replace(startIndex, endIndex, "(" + value + ")");
                startIndex = result.indexOf(placeholder, startIndex + 1);
            }
        }

        String finalExpression = result.toString().replace("z", "x");
        return "(" + finalExpression + ")";
    }
}