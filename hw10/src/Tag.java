import com.oocourse.spec2.main.PersonInterface;
import com.oocourse.spec2.main.TagInterface;

import java.util.HashMap;

public class Tag implements TagInterface {
    private int id;
    private HashMap<Integer, PersonInterface> persons;
    private int ageSum;
    private int agePowerSum;

    public Tag(int id) {
        this.id = id;
        this.persons = new HashMap<>();
        this.ageSum = 0;
        this.agePowerSum = 0;
    }

    @Override
    public int getId() {
        return id;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof TagInterface) {
            return ((TagInterface) obj).getId() == id;
        } else {
            return false;
        }
    }

    @Override
    public void addPerson(PersonInterface person) {
        if (!hasPerson(person)) {
            persons.put(person.getId(), person);
            ageSum += person.getAge();
            agePowerSum += person.getAge() * person.getAge();
        }
    }

    @Override
    public boolean hasPerson(PersonInterface person) {
        return persons.containsKey(person.getId());
    }

    @Override
    public int getAgeMean() {
        int result = 0;
        if (persons.isEmpty()) {
            result = 0;
        } else {
            result =  ageSum / persons.size();
        }
        return result;
    }

    @Override
    public int getAgeVar() {
        int result = 0;
        if (persons.isEmpty()) {
            result = 0;
        } else {
            result =  (agePowerSum - 2 * ageSum * getAgeMean() +
                    persons.size() * getAgeMean() * getAgeMean()) / persons.size();
        }
        return result;
    }

    @Override
    public void delPerson(PersonInterface person) {
        if (hasPerson(person)) {
            persons.remove(person.getId());
            ageSum -= person.getAge();
            agePowerSum -= person.getAge() * person.getAge();
        }
    }

    @Override
    public int getSize() {
        return persons.size();
    }

    @Override
    public int getValueSum() {
        int valueSum = 0;
        for (PersonInterface person : persons.values()) {
            Person person1 = (Person) person;
            for (PersonInterface acquaintance : person1.getAcquaintance().values()) {
                if (hasPerson(acquaintance)) {
                    valueSum += person1.queryValue(acquaintance);
                }
            }
        }
        return valueSum;
    }

    /*--------------------------------------------------------------*/

    public HashMap<Integer, PersonInterface> getPersons() {
        return persons;
    }
}
