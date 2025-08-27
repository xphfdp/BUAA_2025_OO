import com.oocourse.spec3.exceptions.*;
import com.oocourse.spec3.main.*;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.*;

import static org.junit.Assert.*;

@RunWith(Parameterized.class)
public class NetworkTest {
    private final NetworkInterface oldNetwork;
    private final NetworkInterface newNetwork;
    private final List<Integer> remainingEmojiIds = new ArrayList<>();
    private final List<Integer> remainingEmojiHeats = new ArrayList<>();
    private final List<MessageInterface> remainingMessages = new ArrayList<>();
    private final List<Integer> remainingMessageIds = new ArrayList<>();

    public NetworkTest(NetworkInterface oldNetwork, NetworkInterface newNetwork) {
        this.oldNetwork = oldNetwork;
        this.newNetwork = newNetwork;
    }

    /**
     * 测试数据生成
     * for deleteColdEmoji()
     */
    @Parameterized.Parameters
    public static Collection prepareDataForDeleteColdEmoji() {
        int testNum = 100; // 测试轮次，与 NetworkTest 一致
        Object[][] object = new Object[testNum][];
        Random random = new Random(66); // 固定种子，与 NetworkTest 一致
        for (int i = 0; i < testNum; i++) {
            NetworkInterface oldNetwork = new Network();
            NetworkInterface newNetwork = new Network();
            if (i % 10 == 0) {
                generateSpecificNetwork(oldNetwork, newNetwork, random);
            } else {
                generateRandomNetworkForDCE(oldNetwork, newNetwork, random);
            }
            object[i] = new Object[]{oldNetwork, newNetwork};
        }
        return Arrays.asList(object);
    }

    /**
     * 测试deleteColdEmoji()方法
     */
    @Test
    public void testDeleteColdEmoji() {
        Random random = new Random(66);
        int limit = random.nextInt(50); // 随机阈值，范围与 NetworkTest 的关系值类似

        // 计算预期结果
        calculateExpectedEmojiState(((Network) oldNetwork).getMessages(),
                ((Network) oldNetwork).getEmojiIdList(), ((Network) oldNetwork).getEmojiHeatList(), limit);
        int stdAnswer = remainingEmojiIds.size();

        // 调用 deleteColdEmoji 并验证返回值
        int testAnswer = newNetwork.deleteColdEmoji(limit);
        assertEquals("Remaining emoji count mismatch", stdAnswer, testAnswer);

        // 验证表情 ID 和热度
        int[] newEmojiIds = ((Network) newNetwork).getEmojiIdList();
        int[] newEmojiHeats = ((Network) newNetwork).getEmojiHeatList();
        assertEquals("Emoji ID list length mismatch", remainingEmojiIds.size(), newEmojiIds.length);
        assertEquals("Emoji heat list length mismatch", remainingEmojiHeats.size(), newEmojiHeats.length);
        for (int i = 0; i < newEmojiIds.length; i++) {
            assertTrue("Emoji ID should be retained", remainingEmojiIds.contains(newEmojiIds[i]));
            assertEquals("Emoji heat mismatch", remainingEmojiHeats.get(remainingEmojiIds.indexOf(newEmojiIds[i])).intValue(), newEmojiHeats[i]);
        }

        // 验证消息
        MessageInterface[] newMessages = ((Network) newNetwork).getMessages();
        assertEquals("Message count mismatch", remainingMessages.size(), newMessages.length);
        for (MessageInterface newMessage : newMessages) {
            assertTrue("Message should be retained", remainingMessageIds.contains(newMessage.getId()));
            // 查找匹配的预期消息
            MessageInterface expectedMessage = remainingMessages.stream()
                    .filter(m -> m.getId() == newMessage.getId())
                    .findFirst()
                    .orElse(null);
            assertNotNull("Expected message should exist", expectedMessage);
            assertEquals("Message type mismatch", expectedMessage.getType(), newMessage.getType());
            assertEquals("Message person1 mismatch", expectedMessage.getPerson1(), newMessage.getPerson1());
            if (expectedMessage.getType() == 0) {
                assertEquals("Message person2 mismatch", expectedMessage.getPerson2(), newMessage.getPerson2());
            } else {
                assertEquals("Message tag mismatch", expectedMessage.getTag(), newMessage.getTag());
            }
            assertEquals("Message social value mismatch", expectedMessage.getSocialValue(), newMessage.getSocialValue());
            if (expectedMessage instanceof EmojiMessageInterface) {
                assertTrue("Message should be EmojiMessage", newMessage instanceof EmojiMessageInterface);
                assertEquals("Emoji ID mismatch",
                        ((EmojiMessageInterface) expectedMessage).getEmojiId(),
                        ((EmojiMessageInterface) newMessage).getEmojiId());
            } else if (expectedMessage instanceof ForwardMessageInterface) {
                assertTrue("Message should be ForwardMessage", newMessage instanceof ForwardMessageInterface);
                assertEquals("Article ID mismatch",
                        ((ForwardMessageInterface) expectedMessage).getArticleId(),
                        ((ForwardMessageInterface) newMessage).getArticleId());
            } else if (expectedMessage instanceof RedEnvelopeMessageInterface) {
                assertTrue("Message should be RedEnvelopeMessage", newMessage instanceof RedEnvelopeMessageInterface);
                assertEquals("Money mismatch",
                        ((RedEnvelopeMessageInterface) expectedMessage).getMoney(),
                        ((RedEnvelopeMessageInterface) newMessage).getMoney());
            }
        }

        // 验证网络状态不变
        PersonInterface[] oldPersons = ((Network) oldNetwork).getPersons();
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

    /**
     * 测试空网络
     */
    @Test
    public void testEmptyNetworkForDeleteColdEmoji() {
        NetworkInterface network = new Network();
        assertEquals("Empty network should have 0 remaining emoji", 0, network.deleteColdEmoji(10));
    }

    /**
     * 测试无emoji消息网络
     */
    @Test
    public void testNoEmojiMessages() {
        NetworkInterface network = new Network();
        try {
            network.addPerson(new Person(0, "A", 20));
            network.addPerson(new Person(1, "B", 21));
            network.addRelation(0, 1, 100);
            network.storeEmojiId(1);
            network.addMessage(new RedEnvelopeMessage(1, 100, network.getPerson(0), network.getPerson(1)));
        } catch (Exception e) {
            // 忽略异常
        }
        assertEquals("Network with no emoji messages should retain 0 emojis", 0, network.deleteColdEmoji(1));
    }

    /**
     * 测试所有emoji热度为0
     */
    @Test
    public void testAllEmojiEqualZero() {
        NetworkInterface network = new Network();
        try {
            network.addPerson(new Person(0, "A", 20));
            network.addPerson(new Person(1, "B", 21));
            network.addRelation(0, 1, 100);
            network.storeEmojiId(1);
            network.addMessage(new EmojiMessage(1, 1, network.getPerson(0), network.getPerson(1)));
            // 不进行sendMessage(), 表情 1 热度 = 0
        } catch (Exception e) {
            // 忽略异常
        }
        assertEquals("All emojis below limit should retain 1 emojis", 1, network.deleteColdEmoji(0));
        assertEquals("Emoji ID list should not be empty", 1, ((Network) network).getEmojiIdList().length);
        assertEquals("Emoji heat list should not be empty", 1, ((Network) network).getEmojiHeatList().length);
        assertEquals("Messages list should not be empty", 1, ((Network) network).getMessages().length);
    }

    /**
     * 测试所有emoji热度低于阈值
     */
    @Test
    public void testAllEmojiBelowLimit() {
        NetworkInterface network = new Network();
        try {
            network.addPerson(new Person(0, "A", 20));
            network.addPerson(new Person(1, "B", 21));
            network.addRelation(0, 1, 100);
            network.storeEmojiId(1);
            network.addMessage(new EmojiMessage(1, 1, network.getPerson(0), network.getPerson(0)));
            network.sendMessage(1); // 表情 1 热度 = 1
        } catch (Exception e) {
            // 忽略异常
        }
        assertEquals("All emojis below limit should retain 0 emojis", 0, network.deleteColdEmoji(2));
        assertEquals("Emoji ID list should be empty", 0, ((Network) network).getEmojiIdList().length);
        assertEquals("Emoji heat list should be empty", 0, ((Network) network).getEmojiHeatList().length);
        assertEquals("Messages list should be empty", 0, ((Network) network).getMessages().length);
    }

    /**
     * 测试所有emoji热度高于阈值
     */
    @Test
    public void testAllEmojiAboveLimit() {
        NetworkInterface network = new Network();
        try {
            network.addPerson(new Person(0, "A", 20));
            network.addPerson(new Person(1, "B", 21));
            network.addRelation(0, 1, 100);
            network.storeEmojiId(1);
            for (int i = 1; i <= 5; i++) {
                network.addMessage(new EmojiMessage(i, 1, network.getPerson(0), network.getPerson(1)));
                network.sendMessage(i); // 表情 1 热度 = 5
            }
        } catch (Exception e) {
            // 忽略异常
        }
        assertEquals("All emojis above limit should retain 1 emoji", 1, network.deleteColdEmoji(5));
        assertEquals("Emoji ID list should have 1 element", 1, ((Network) network).getEmojiIdList().length);
        assertEquals("Emoji heat list should have 1 element", 1, ((Network) network).getEmojiHeatList().length);
    }

    /**
     * 测试所有emoji热度等于阈值
     */
    @Test
    public void testAllEmojiEqualLimit() {
        NetworkInterface network = new Network();
        try {
            network.addPerson(new Person(0, "A", 20));
            network.addPerson(new Person(1, "B", 21));
            network.addRelation(0, 1, 100);
            network.storeEmojiId(1);
            for (int i = 1; i <= 5; i++) {
                network.addMessage(new EmojiMessage(i, 1, network.getPerson(0), network.getPerson(1)));
                network.sendMessage(i); // 表情 1 热度 = 5
            }
        } catch (Exception e) {
            fail("Setup failed: " + e.getMessage());
        }
        assertEquals("Emoji at limit should retain 1 emoji", 1, network.deleteColdEmoji(5));
        assertEquals("Emoji ID list should have 1 element", 1, ((Network) network).getEmojiIdList().length);
        assertEquals("Emoji heat list should have 1 element", 1, ((Network) network).getEmojiHeatList().length);
    }

    /**
     * 测试Tag消息
     */
    @Test
    public void testTagMessages() {
        NetworkInterface network = new Network();
        try {
            network.addPerson(new Person(0, "A", 20));
            network.addPerson(new Person(1, "B", 21));
            network.addPerson(new Person(2, "C", 22));
            network.addRelation(0, 1, 100);
            network.addRelation(0, 2, 100);
            network.storeEmojiId(1);
            Tag tag = new Tag(1);
            network.addTag(0, tag);
            network.addPersonToTag(1, 0, 1);
            network.addPersonToTag(2, 0, 1);
            network.addMessage(new EmojiMessage(1, 1, network.getPerson(0), tag));
            network.sendMessage(1); // 表情 1 热度 = 1
        } catch (Exception e) {
            fail("Setup failed: " + e.getMessage());
        }
        assertEquals("Tag message with emoji below limit should retain 0 emojis", 0, network.deleteColdEmoji(2));
        assertEquals("Emoji ID list should be empty", 0, ((Network) network).getEmojiIdList().length);
        assertEquals("Emoji heat list should be empty", 0, ((Network) network).getEmojiHeatList().length);
        assertEquals("Messages list should be empty", 0, ((Network) network).getMessages().length);
    }

    /*-----------------------------数据生成-----------------------------*/

    /**
     * 计算预期的emoji状态
     */
    private void calculateExpectedEmojiState(MessageInterface[] messages, int[] emojiIds, int[] emojiHeats, int limit) {
        for (int i = 0; i < emojiIds.length; i++) {
            if (emojiHeats[i] >= limit) {
                remainingEmojiIds.add(emojiIds[i]);
                remainingEmojiHeats.add(emojiHeats[i]);
            }
        }
        for (MessageInterface message : messages) {
            if (!(message instanceof EmojiMessageInterface) ||
                    remainingEmojiIds.contains(((EmojiMessageInterface) message).getEmojiId())) {
                remainingMessages.add(message);
                remainingMessageIds.add(message.getId());
            }
        }
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
     * 生成特定网络，确保特定emoji热度分布
     */
    private static void generateSpecificNetwork(NetworkInterface oldNetwork, NetworkInterface newNetwork, Random random) {
        int n = 20;
        // 添加人员
        for (int i = 0; i < n; i++) {
            try {
                oldNetwork.addPerson(new Person(i, "Person" + i, 70 - i));
                newNetwork.addPerson(new Person(i, "Person" + i, 70 - i));
            } catch (EqualPersonIdException e) {
                // 忽略异常
            }
        }
        // 添加关系
        try {
            for (int i = 0; i < n; i++) {
                for (int j = i + 1; j < n; j++) {
                    if (random.nextBoolean()) {
                        oldNetwork.addRelation(i, j, random.nextInt(100) + 1);
                        newNetwork.addRelation(i, j, random.nextInt(100) + 1);
                    }
                }
            }
        } catch (Exception e) {
            // 忽略异常
        }
        // 添加标签
        try {
            Tag tag = new Tag(1);
            oldNetwork.addTag(0, tag);
            newNetwork.addTag(0, tag);
            for (int i = 1; i < 5; i++) {
                oldNetwork.addPersonToTag(i, 0, 1);
                newNetwork.addPersonToTag(i, 0, 1);
            }
        } catch (Exception e) {
            // 忽略异常
        }
        // 添加表情 ID
        try {
            for (int i = 1; i <= 10; i++) {
                oldNetwork.storeEmojiId(i);
                newNetwork.storeEmojiId(i);
            }
        } catch (EqualEmojiIdException e) {
            // 忽略异常
        }
        // 添加文章
        try {
            oldNetwork.createOfficialAccount(1, 0, "Account1");
            newNetwork.createOfficialAccount(1, 0, "Account1");
            for (int i = 1; i <= 10; i++) {
                oldNetwork.contributeArticle(1, 0, i);
                newNetwork.contributeArticle(1, 0, i);
            }
        } catch (Exception e) {
            // 忽略异常
        }
        // 添加消息，确保表情 1 热度高，表情 2 热度低
        try {
            // 高热度表情消息
            for (int i = 1; i <= 5; i++) {
                oldNetwork.addMessage(new EmojiMessage(i, 1, oldNetwork.getPerson(0), oldNetwork.getPerson(1)));
                newNetwork.addMessage(new EmojiMessage(i, 1, newNetwork.getPerson(0), newNetwork.getPerson(1)));
                oldNetwork.sendMessage(i); // 表情 1 热度 = 5
                newNetwork.sendMessage(i);
            }
            // 低热度表情消息
            oldNetwork.addMessage(new EmojiMessage(6, 2, oldNetwork.getPerson(0), oldNetwork.getPerson(1)));
            newNetwork.addMessage(new EmojiMessage(6, 2, newNetwork.getPerson(0), newNetwork.getPerson(1)));
            oldNetwork.sendMessage(6); // 表情 2 热度 = 1
            newNetwork.sendMessage(6);
            // emoji消息
            oldNetwork.addMessage(new EmojiMessage(7, 1, oldNetwork.getPerson(0), oldNetwork.getPerson(0).getTag(1)));
            newNetwork.addMessage(new EmojiMessage(7, 1, newNetwork.getPerson(0), newNetwork.getPerson(0).getTag(1)));
            oldNetwork.sendMessage(7); // 表情 1 热度 += 1
            newNetwork.sendMessage(7);
            // 非emoji消息
            oldNetwork.addMessage(new ForwardMessage(8, 1, oldNetwork.getPerson(0), oldNetwork.getPerson(1)));
            newNetwork.addMessage(new ForwardMessage(8, 1, newNetwork.getPerson(0), newNetwork.getPerson(1)));
            oldNetwork.addMessage(new RedEnvelopeMessage(9, 100, oldNetwork.getPerson(0), oldNetwork.getPerson(1)));
            newNetwork.addMessage(new RedEnvelopeMessage(9, 100, newNetwork.getPerson(0), newNetwork.getPerson(1)));
        } catch (Exception e) {
            // 忽略异常
        }
    }

    /**
     * 随机生成网络
     */
    private static void generateRandomNetworkForDCE(NetworkInterface oldNetwork, NetworkInterface newNetwork, Random random) {
        int n = 100; // 大规模网络，与 generateRandomNetwork 一致
        // 添加人员
        for (int i = 0; i < n; i++) {
            try {
                oldNetwork.addPerson(new Person(i, "Person" + i, 70 - i));
                newNetwork.addPerson(new Person(i, "Person" + i, 70 - i));
            } catch (EqualPersonIdException e) {
                fail("Unexpected EqualPersonIdException: " + e.getMessage());
            }
        }
        // 添加关系
        try {
            for (int i = 0; i < 300; i++) {
                int id1 = random.nextInt(n);
                int id2 = random.nextInt(n);
                if (id1 != id2) {
                    oldNetwork.addRelation(id1, id2, random.nextInt(100) + 1);
                    newNetwork.addRelation(id1, id2, random.nextInt(100) + 1);
                }
            }
        } catch (Exception e) {
            // 忽略异常
        }
        // 添加标签
        try {
            for (int i = 1; i <= 10; i++) {
                Tag tag = new Tag(i);
                oldNetwork.addTag(0, tag);
                newNetwork.addTag(0, tag);
                for (int j = 1; j <= 5; j++) {
                    oldNetwork.addPersonToTag(j, 0, i);
                    newNetwork.addPersonToTag(j, 0, i);
                }
            }
        } catch (Exception e) {
            // 忽略异常
        }
        // 添加表情 ID
        try {
            for (int i = 1; i <= 50; i++) {
                oldNetwork.storeEmojiId(i);
                newNetwork.storeEmojiId(i);
            }
        } catch (EqualEmojiIdException e) {
            // 忽略异常
        }
        // 添加文章
        try {
            oldNetwork.createOfficialAccount(1, 0, "Account1");
            newNetwork.createOfficialAccount(1, 0, "Account1");
            for (int i = 1; i <= 50; i++) {
                oldNetwork.contributeArticle(1, 0, i);
                newNetwork.contributeArticle(1, 0, i);
            }
        } catch (Exception e) {
            // 忽略异常
        }
        // 添加消息
        try {
            int messageId = 1;
            for (int i = 0; i < 300; i++) {
                int id1 = random.nextInt(n);
                int id2 = random.nextInt(n);
                int emojiId = random.nextInt(50) + 1;
                int articleId = random.nextInt(50) + 1;
                int money = random.nextInt(100) + 1;
                int tagId = random.nextInt(10) + 1;
                int messageType = random.nextInt(4); // 0: Emoji, 1: Forward, 2: RedEnvelope, 3: Emoji to Tag
                if (messageType == 0) {
                    oldNetwork.addMessage(new EmojiMessage(messageId, emojiId, oldNetwork.getPerson(id1), oldNetwork.getPerson(id2)));
                    newNetwork.addMessage(new EmojiMessage(messageId, emojiId, newNetwork.getPerson(id1), newNetwork.getPerson(id2)));
                } else if (messageType == 1) {
                    oldNetwork.addMessage(new ForwardMessage(messageId, articleId, oldNetwork.getPerson(id1), oldNetwork.getPerson(id2)));
                    newNetwork.addMessage(new ForwardMessage(messageId, articleId, newNetwork.getPerson(id1), newNetwork.getPerson(id2)));
                } else if (messageType == 2) {
                    oldNetwork.addMessage(new RedEnvelopeMessage(messageId, money, oldNetwork.getPerson(id1), oldNetwork.getPerson(id2)));
                    newNetwork.addMessage(new RedEnvelopeMessage(messageId, money, newNetwork.getPerson(id1), newNetwork.getPerson(id2)));
                } else if (messageType == 3) {
                    oldNetwork.addMessage(new EmojiMessage(messageId, emojiId, oldNetwork.getPerson(0), oldNetwork.getPerson(0).getTag(tagId)));
                    newNetwork.addMessage(new EmojiMessage(messageId, emojiId, newNetwork.getPerson(0), newNetwork.getPerson(0).getTag(tagId)));
                }
                if (random.nextBoolean()) {
                    oldNetwork.sendMessage(messageId);
                    newNetwork.sendMessage(messageId);
                }
                messageId++;
            }
        } catch (Exception e) {
            // 忽略异常
        }
    }
}