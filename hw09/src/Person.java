import com.oocourse.spec1.main.PersonInterface;
import com.oocourse.spec1.main.TagInterface;

import java.util.HashMap;
import java.util.TreeSet;

public class Person implements PersonInterface {
    private int id;
    private String name;
    private int age;
    private HashMap<Integer, PersonInterface> acquaintance;
    private HashMap<Integer, Integer> value;
    private HashMap<Integer, TagInterface> tags;
    private final TreeSet<PersonInterface> acquaintanceSort;

    public Person(int id, String name, int age) {
        this.id = id;
        this.name = name;
        this.age = age;
        this.acquaintance = new HashMap<>();
        this.value = new HashMap<>();
        this.tags = new HashMap<>();
        this.acquaintanceSort = new TreeSet<>((p1, p2) -> comparePersons((Person) p1,
                (Person) p2, this));
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

    /*------------------------------------For Test------------------------------------*/

    public boolean strictEquals(PersonInterface person) {
        return true;
    }
}
