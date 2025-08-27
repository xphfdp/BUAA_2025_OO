import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class NorDefiner {
    private static HashMap<Character, String> norFuncMap = new HashMap<>(); // key存储函数名，value为定义式
    private static HashMap<Character, ArrayList<String>> norParamMap = new HashMap<>();

    public static void addNorFunc(String input) {
        /*TODO:获取norFunc的定义式和形参列表，并存入相应的HashMap中*/
        Pattern pattern = Pattern.compile("([gh])\\((.*?)\\)=(.+)");
        Matcher matcher = pattern.matcher(input.trim());
        if (matcher.find()) {
            String funcName = matcher.group(1);
            String params = matcher.group(2);
            String definition = matcher.group(3).trim();

            norFuncMap.put(funcName.charAt(0), definition);
            ArrayList<String> paramList = new ArrayList<>();
            for (String param : params.split(",")) {
                paramList.add(param.trim());
            }
            norParamMap.put(funcName.charAt(0), paramList);
        } else {
            throw new RuntimeException("Invalid function definition: " + input);
        }
    }

    public static String callNorFunc(Character name, ArrayList<Factor> actualParas) {
        /*TODO:将实参带入到norFunc的定义式中，并返回计算结果*/
        String definition = norFuncMap.get(name);
        ArrayList<String> params = norParamMap.get(name);
        for (int i = 0; i < actualParas.size() && i < params.size(); i++) {
            if (i == 0) {
                definition = definition.replace(params.get(i),
                        "(" + actualParas.get(i).toPoly().toString().replace("x", "z") + ")");
            } else {
                definition = definition.replace(params.get(i),
                        "(" + actualParas.get(i).toPoly().toString() + ")");
            }
        }
        return ("(" + definition.replace("z", "x") + ")");
    }
}
