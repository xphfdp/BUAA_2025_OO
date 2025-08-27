import java.math.BigInteger;

public class Var implements Factor {
    @Override
    public Poly toPoly() {
        return new Poly().addTerm(1, BigInteger.ONE);
    }
}