import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class RecDefiner {
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

    public static String callFunc(Character index, ArrayList<Factor> actualParas) {
        if (index == '0' || index == '1') {
            String s = funcMap.get(index);
            ArrayList<String> params = paramMap.get(index);
            for (int i = 0; i < params.size() && i < actualParas.size(); i++) {
                if (i == 0) {
                    s = s.replace(params.get(i), "(" +
                            actualParas.get(i).toPoly().toString().replace("x", "z") + ")");
                } else if (i == 1) {
                    s = s.replace(params.get(i), "(" +
                            actualParas.get(i).toPoly().toString() + ")");
                }
            }
            return ("(" + s.replace("z", "x") + ")");
        } else {
            String s = funcMap.get('n');
            Character sh = (char) (index - 1);
            Character sh2 = (char) (index - 2);
            s = s.replace("n-1", sh.toString());
            s = s.replace("n-2", sh2.toString());
            ArrayList<String> params = paramMap.get('0');
            for (int i = 0; i < actualParas.size() && i < params.size(); i++) {
                s = s.replace(params.get(i), "(" +
                        actualParas.get(i).toPoly().toString().replace("x","z") + ")");
            }
            return ("(" + s.replace("z", "x") + ")");
        }
    }
}