import com.oocourse.spec1.exceptions.EqualPersonIdException;
import com.oocourse.spec1.exceptions.EqualRelationException;
import com.oocourse.spec1.exceptions.PersonIdNotFoundException;
import com.oocourse.spec1.main.NetworkInterface;
import com.oocourse.spec1.main.PersonInterface;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Random;
import java.util.ArrayList;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

@RunWith(Parameterized.class)
public class NetworkTest {
    private final NetworkInterface oldNetwork;
    private final NetworkInterface newNetwork;

    public NetworkTest(NetworkInterface oldNetwork, NetworkInterface newNetwork) {
        this.oldNetwork = oldNetwork;
        this.newNetwork = newNetwork;
    }

    @Parameterized.Parameters
    public static Collection prepareData() {
        int testNum = 100; // 测试轮次，视情况修改
        Object[][] object = new Object[testNum][];
        Random random = new Random(66); // 固定种子,视情况修改
        for (int i = 0; i < testNum; i++) {
            NetworkInterface oldNetwork = new Network();
            NetworkInterface newNetwork = new Network();
            if (i % 10 == 0) {
                generateTriangleNetwork(oldNetwork, newNetwork, random);
            } else {
                generateRandomNetwork(oldNetwork, newNetwork, random);
            }
            object[i] = new Object[]{oldNetwork, newNetwork};
        }
        return Arrays.asList(object);
    }

    /**
     * 测试方法
     */
    @Test
    public void testQueryTripleSum() {
        PersonInterface[] oldPersons = ((Network) oldNetwork).getPersons();
        int stdAnswer = calculateTripleSum(oldPersons);
        int testAnswer = newNetwork.queryTripleSum();
        assertEquals("Triple sum mismatch", stdAnswer, testAnswer);

        PersonInterface[] newPersons = ((Network) newNetwork).getPersons();
        assertEquals("Person count mismatch", oldPersons.length, newPersons.length);
        for (int i = 0; i < oldPersons.length; i++) {
            assertPersonEquals(oldPersons[i], newPersons[i]);
        }
        for (int i = 0; i < oldPersons.length; i++) {
            for (int j = 0; j < oldPersons.length; j++) {
                if (i != j) {
                    assertEquals("Relation mismatch",
                            oldPersons[i].isLinked(oldPersons[j]),
                            newPersons[i].isLinked(newPersons[j]));
                }
            }
        }
    }

    @Test
    public void testEmptyNetwork() {
        NetworkInterface network = new Network();
        assertEquals("Empty network should have 0 triangles", 0, network.queryTripleSum());
    }

    @Test
    public void testSinglePersonNetwork() {
        NetworkInterface network = new Network();
        try {
            network.addPerson(new Person(0, "A", 20));
        } catch (EqualPersonIdException e) {
            fail("Setup failed: " + e.getMessage());
        }
        assertEquals("Single person network should have 0 triangles", 0,
                network.queryTripleSum());
    }

    @Test
    public void testTriangleNetwork() {
        NetworkInterface network = new Network();
        try {
            network.addPerson(new Person(0, "A", 20));
            network.addPerson(new Person(1, "B", 21));
            network.addPerson(new Person(2, "C", 22));
            network.addRelation(0, 1, 1);
            network.addRelation(1, 2, 1);
            network.addRelation(2, 0, 1);
        } catch (Exception e) {
            fail("Setup failed: " + e.getMessage());
        }
        assertEquals("Triangle network should have 1 triangle", 1, network.queryTripleSum());
    }

    @Test
    public void testRelationModification() {
        NetworkInterface network = new Network();
        try {
            network.addPerson(new Person(0, "A", 20));
            network.addPerson(new Person(1, "B", 21));
            network.addPerson(new Person(2, "C", 22));
            network.addRelation(0, 1, 1);
            network.addRelation(1, 2, 1);
            network.addRelation(2, 0, 1);
            assertEquals("Initial triangle network should have 1 triangle", 1,
                    network.queryTripleSum());
            network.modifyRelation(0, 1, -1);
            assertEquals("After removing edge, network should have 0 triangles", 0,
                    network.queryTripleSum());
        } catch (Exception e) {
            fail("Setup failed: " + e.getMessage());
        }
    }

    /*-----------------------------数据生成-----------------------------*/

    /**
     * 计算社交网络中三角关系网的数量
     */
    private int calculateTripleSum(PersonInterface[] persons) {
        int count = 0;
        for (int i = 0; i < persons.length; i++) {
            int id1 = persons[i].getId();
            HashMap<Integer, PersonInterface> neighbors1 = ((Person) persons[i]).getAcquaintance();
            for (PersonInterface p2 : neighbors1.values()) {
                int id2 = p2.getId();
                if (id2 > id1) {
                    HashMap<Integer, PersonInterface> neighbors2 = ((Person) p2).getAcquaintance();
                    for (PersonInterface p3 : neighbors2.values()) {
                        int id3 = p3.getId();
                        if (id3 > id2 && persons[i].isLinked(p3)) {
                            count++;
                        }
                    }
                }
            }
        }
        return count;
    }

    /**
     * 检测人员一致性
     */
    private void assertPersonEquals(PersonInterface p1, PersonInterface p2) {
        assertEquals("ID mismatch", p1.getId(), p2.getId());
        assertEquals("Name mismatch", p1.getName(), p2.getName());
        assertEquals("Age mismatch", p1.getAge(), p2.getAge());
    }

    /**
     * 生成存在三角关系网的network
     */
    private static void generateTriangleNetwork(NetworkInterface oldNetwork,
                                                NetworkInterface newNetwork, Random random) {
        int n = 20;
        for (int i = 0; i < n; i++) {
            try {
                oldNetwork.addPerson(new Person(i, "name" + i, 70 - i));
                newNetwork.addPerson(new Person(i, "name" + i, 70 - i));
            } catch (EqualPersonIdException e) {
                fail("Unexpected EqualPersonIdException: " + e.getMessage());
            }
        }
        try {
            // 添加针对性关系，保证必然存在三角关系
            oldNetwork.addRelation(0, 1, 1);
            oldNetwork.addRelation(1, 2, 1);
            oldNetwork.addRelation(2, 0, 1);
            newNetwork.addRelation(0, 1, 1);
            newNetwork.addRelation(1, 2, 1);
            newNetwork.addRelation(2, 0, 1);
            // 添加随机关系
            for (int i = 0; i < 50; i++) {
                int id1 = random.nextInt(n);
                int id2 = random.nextInt(n);
                if (id1 != id2) {
                    try {
                        oldNetwork.addRelation(id1, id2, 1);
                        newNetwork.addRelation(id1, id2, 1);
                    } catch (EqualRelationException | PersonIdNotFoundException e) {
                        // 忽略异常
                    }
                }
            }
        } catch (Exception e) {
            fail("Setup failed: " + e.getMessage());
        }
    }

    /**
     * 随机生成关系网，不保证存在三角关系网
     */
    private static void generateRandomNetwork(NetworkInterface oldNetwork,
                                              NetworkInterface newNetwork, Random random) {
        int n = 100;
        ArrayList<Integer> list = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            list.add(i);
            try {
                oldNetwork.addPerson(new Person(i, "name-" + i, 0));
                newNetwork.addPerson(new Person(i, "name-" + i, 0));
            } catch (EqualPersonIdException e) {
                fail("Unexpected EqualPersonIdException: " + e.getMessage());
            }
        }
        for (int i = 0; i < 300; i++) {
            int index1 = random.nextInt(n);
            int index2 = random.nextInt(n);
            if (index1 != index2) {
                try {
                    oldNetwork.addRelation(list.get(index1), list.get(index2), 1);
                    newNetwork.addRelation(list.get(index1), list.get(index2), 1);
                } catch (EqualRelationException | PersonIdNotFoundException e) {
                    // 忽略异常
                }
            }
        }
    }

}