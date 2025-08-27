import java.math.BigInteger;
import java.util.HashMap;

public class Var implements Factor {
    @Override
    public Poly toPoly() {
        return new Poly(new Mono(BigInteger.ONE, BigInteger.ONE, new HashMap<>(), new HashMap<>()
        ));
    }

    @Override
    public String toString() {
        return "x";
    }
}