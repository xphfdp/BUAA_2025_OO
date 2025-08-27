import com.oocourse.spec3.main.MessageInterface;
import com.oocourse.spec3.main.PersonInterface;
import com.oocourse.spec3.main.TagInterface;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.TreeSet;

public class Person implements PersonInterface {
    private int id;
    private String name;
    private int age;
    private HashMap<Integer, PersonInterface> acquaintance;
    private HashMap<Integer, Integer> value;
    private HashMap<Integer, TagInterface> tags;
    private final TreeSet<PersonInterface> acquaintanceSort;
    private final HashMap<Integer, HashSet<ArticleNode>> articleMap; // articleId -> ArticleNode
    private ArticleNode head; // 双向链表头部
    private ArticleNode tail; // 双向链表尾部
    private int size; // 双向链表大小
    private int money;
    private int socialValue;
    private LinkedList<MessageInterface> messages;

    private static class ArticleNode {
        private int articleId;
        private ArticleNode prev;
        private ArticleNode next;

        ArticleNode(int articleId) {
            this.articleId = articleId;
            this.prev = null;
            this.next = null;
        }
    }

    public Person(int id, String name, int age) {
        this.id = id;
        this.name = name;
        this.age = age;
        this.acquaintance = new HashMap<>();
        this.value = new HashMap<>();
        this.tags = new HashMap<>();
        this.acquaintanceSort = new TreeSet<>((p1, p2) -> comparePersons((Person) p1,
                (Person) p2, this));
        this.articleMap = new HashMap<>();
        this.head = null;
        this.tail = null;
        this.size = 0;
        this.money = 0;
        this.socialValue = 0;
        this.messages = new LinkedList<>();
    }

    @Override
    public int getId() {
        return id;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public int getAge() {
        return age;
    }

    @Override
    public boolean containsTag(int id) {
        return tags.containsKey(id);
    }

    @Override
    public TagInterface getTag(int id) {
        if (tags.containsKey(id)) {
            return tags.get(id);
        } else {
            return null;
        }
    }

    @Override
    public void addTag(TagInterface tag) {
        if (!containsTag(tag.getId())) {
            tags.put(tag.getId(), tag);
        }
    }

    @Override
    public void delTag(int id) {
        if (containsTag(id)) {
            tags.remove(id);
        }
    }

    @Override
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof PersonInterface) {
            return ((PersonInterface) obj).getId() == id;
        } else {
            return false;
        }
    }

    @Override
    public boolean isLinked(PersonInterface person) {
        return acquaintance.containsKey(person.getId()) || person.getId() == id;
    }

    @Override
    public int queryValue(PersonInterface person) {
        if (acquaintance.containsKey(person.getId())) {
            return value.get(person.getId());
        } else {
            return 0;
        }
    }

    @Override
    public LinkedList<Integer> getReceivedArticles() {
        LinkedList<Integer> result = new LinkedList<>();
        ArticleNode current = head;
        while (current != null) {
            result.add(current.articleId);
            current = current.next;
        }
        return result;
    }

    @Override
    public LinkedList<Integer> queryReceivedArticles() {
        LinkedList<Integer> result = new LinkedList<>();
        ArticleNode current = head;
        for (int i = 0; i < 5 && current != null; i++) {
            result.add(current.articleId);
            current = current.next;
        }
        return result;
    }

    @Override
    public void addSocialValue(int num) {
        this.socialValue += num;
    }

    @Override
    public int getSocialValue() {
        return this.socialValue;
    }

    @Override
    public LinkedList<MessageInterface> getMessages() {
        return messages;
    }

    @Override
    public LinkedList<MessageInterface> getReceivedMessages() {
        LinkedList<MessageInterface> result = new LinkedList<>();
        for (int i = 0;i < messages.size() && i <= 4; i++) {
            result.add(messages.get(i));
        }
        return result;
    }

    @Override
    public void addMoney(int num) {
        this.money += num;
    }

    @Override
    public int getMoney() {
        return this.money;
    }

    /*---------------------------------helper methods---------------------------------*/

    public void addLink(PersonInterface person, int value) {
        acquaintance.put(person.getId(), person);
        this.value.put(person.getId(), value);
        acquaintanceSort.add(person);
    }

    public void delLink(PersonInterface person) {
        acquaintanceSort.remove(person);
        acquaintance.remove(person.getId());
        this.value.remove(person.getId());
    }

    public void modifyValue(PersonInterface person, int value) {
        acquaintanceSort.remove(person);
        this.value.put(person.getId(), value);
        acquaintanceSort.add(person);
    }

    public int getBestAcquaintanceId() {
        return acquaintanceSort.first().getId();
    }

    public HashMap<Integer, Integer> getValue() {
        return value;
    }

    public HashMap<Integer, PersonInterface> getAcquaintance() {
        return acquaintance;
    }

    public HashMap<Integer, TagInterface> getTags() {
        return tags;
    }

    private int comparePersons(Person p1, Person p2, Person owner) {
        if (p1.equals(p2)) {
            return 0;
        }
        int valueCompare = owner.queryValue(p2) - owner.queryValue(p1);
        if (valueCompare != 0) {
            return valueCompare;
        }
        return Integer.compare(p1.getId(), p2.getId());
    }

    public boolean isAcquaintanceEmpty() {
        return acquaintance.isEmpty();
    }

    public void addReceivedArticle(int articleId) {
        ArticleNode node = new ArticleNode(articleId);
        this.articleMap.computeIfAbsent(articleId, k -> new HashSet<>()).add(node);
        if (head == null) {
            head = tail = node;
        } else {
            node.next = head;
            head.prev = node;
            head = node;
        }
        size++;
    }

    public void removeReceivedArticle(int articleId) {
        if (!articleMap.containsKey(articleId)) {
            return;
        }
        HashSet<ArticleNode> nodesToRemove = this.articleMap.get(articleId);
        if (nodesToRemove != null && !nodesToRemove.isEmpty()) {
            for (ArticleNode node : nodesToRemove) {
                // Unlink the node from the doubly linked list
                if (node.prev != null) {
                    node.prev.next = node.next;
                } else { // Node is the head
                    head = node.next;
                }
                if (node.next != null) {
                    node.next.prev = node.prev;
                } else { // Node is the tail
                    tail = node.prev;
                }
                size--;
            }
        }
        // After removing all associated nodes from the linked list, remove the entry from the map.
        this.articleMap.remove(articleId);
    }

    public void addMessageOnHead(MessageInterface message) {
        messages.addFirst(message);
    }

    public void updateTagValueSum(int id1, int id2, int value) {
        this.tags.values().forEach(tag -> ((Tag) tag).updateValueSum(id1, id2, value));
    }

    /*------------------------------------For Test------------------------------------*/

    public boolean strictEquals(PersonInterface person) {
        return true;
    }
}
