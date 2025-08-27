
import com.oocourse.spec1.exceptions.EqualPersonIdException;
import com.oocourse.spec1.exceptions.EqualRelationException;
import com.oocourse.spec1.exceptions.PersonIdNotFoundException;
import com.oocourse.spec1.exceptions.RelationNotFoundException;
import com.oocourse.spec1.exceptions.EqualTagIdException;
import com.oocourse.spec1.exceptions.TagIdNotFoundException;
import com.oocourse.spec1.exceptions.AcquaintanceNotFoundException;
import com.oocourse.spec1.main.NetworkInterface;
import com.oocourse.spec1.main.PersonInterface;
import com.oocourse.spec1.main.TagInterface;

import java.util.HashMap;
import java.util.HashSet;

public class Network implements NetworkInterface {
    private HashMap<Integer, PersonInterface> persons;
    private int tripleSum;
    private DisjointSet disjointSet;
    private boolean disjointSetNeedReset;

    public Network() {
        this.persons = new HashMap<>();
        this.tripleSum = 0;
        this.disjointSet = new DisjointSet();
        this.disjointSetNeedReset = false;
    }

    @Override
    public boolean containsPerson(int id) {
        return persons.containsKey(id);
    }

    @Override
    public PersonInterface getPerson(int id) {
        if (containsPerson(id)) {
            return persons.get(id);
        } else {
            return null;
        }
    }

    @Override
    public void addPerson(PersonInterface person) throws EqualPersonIdException {
        if (persons.containsKey(person.getId())) {
            throw new EqualPersonIdException(person.getId());
        } else {
            persons.put(person.getId(), person);
            disjointSet.makeSet(person.getId());
        }
    }

    @Override
    public void addRelation(int id1, int id2, int value) throws PersonIdNotFoundException,
            EqualRelationException {
        if (!containsPerson(id1)) {
            throw new PersonIdNotFoundException(id1);
        }
        if (!containsPerson(id2)) {
            throw new PersonIdNotFoundException(id2);
        }
        if (getPerson(id1).isLinked(getPerson(id2))) {
            throw new EqualRelationException(id1, id2);
        }
        ((Person) getPerson(id1)).addLink(getPerson(id2), value);
        ((Person) getPerson(id2)).addLink(getPerson(id1), value);
        disjointSet.merge(id1, id2);
        disjointSet.addEdge(id1, id2);
        HashSet<Integer> neighbors1 = new HashSet<>(((Person) getPerson(id1)).
                getAcquaintance().keySet());
        neighbors1.retainAll(((Person) getPerson(id2)).getAcquaintance().keySet());
        tripleSum += neighbors1.size();
    }

    @Override
    public void modifyRelation(int id1, int id2, int value) throws PersonIdNotFoundException,
            EqualPersonIdException, RelationNotFoundException {
        if (!containsPerson(id1)) {
            throw new PersonIdNotFoundException(id1);
        }
        if (!containsPerson(id2)) {
            throw new PersonIdNotFoundException(id2);
        }
        if (id1 == id2) {
            throw new EqualPersonIdException(id1);
        }
        if (!getPerson(id1).isLinked(getPerson(id2))) {
            throw new RelationNotFoundException(id1, id2);
        }
        int oldValue = queryValue(id1, id2);
        int newValue = oldValue + value;
        if (newValue > 0) {
            ((Person) getPerson(id1)).modifyValue(getPerson(id2), newValue);
            ((Person) getPerson(id2)).modifyValue(getPerson(id1), newValue);
        } else {
            HashSet<Integer> neighbors1 = new HashSet<>(((Person) getPerson(id1)).
                    getAcquaintance().keySet());
            neighbors1.retainAll(((Person) getPerson(id2)).getAcquaintance().keySet());
            tripleSum -= neighbors1.size();
            disjointSet.removeEdge(id1, id2);
            disjointSetNeedReset = true;
            ((Person) getPerson(id1)).delLink(getPerson(id2));
            ((Person) getPerson(id2)).delLink(getPerson(id1));
            for (TagInterface tag : ((Person) getPerson(id1)).getTags().values()) {
                ((Tag) tag).delPerson(getPerson(id2));
            }
            for (TagInterface tag : ((Person) getPerson(id2)).getTags().values()) {
                ((Tag) tag).delPerson(getPerson(id1));
            }
        }
    }

    @Override
    public int queryValue(int id1, int id2) throws PersonIdNotFoundException,
            RelationNotFoundException {
        if (!containsPerson(id1)) {
            throw new PersonIdNotFoundException(id1);
        }
        if (!containsPerson(id2)) {
            throw new PersonIdNotFoundException(id2);
        }
        if (!getPerson(id1).isLinked(getPerson(id2))) {
            throw new RelationNotFoundException(id1, id2);
        }
        return getPerson(id1).queryValue(getPerson(id2));
    }

    @Override
    public boolean isCircle(int id1, int id2) throws PersonIdNotFoundException {
        if (!containsPerson(id1)) {
            throw new PersonIdNotFoundException(id1);
        }
        if (!containsPerson(id2)) {
            throw new PersonIdNotFoundException(id2);
        }
        if (disjointSetNeedReset) {
            disjointSet.initReset();
            for (PersonInterface person : persons.values()) {
                disjointSet.makeSet(person.getId());
            }
            disjointSet.reset();
            disjointSetNeedReset = false;
        }
        return disjointSet.find(id1) == disjointSet.find(id2);
    }

    @Override
    public int queryTripleSum() {
        return tripleSum;
    }

    @Override
    public void addTag(int personId, TagInterface tag) throws PersonIdNotFoundException,
            EqualTagIdException {
        if (!containsPerson(personId)) {
            throw new PersonIdNotFoundException(personId);
        }
        if (getPerson(personId).containsTag(tag.getId())) {
            throw new EqualTagIdException(tag.getId());
        }
        ((Person) getPerson(personId)).addTag(tag);
    }

    @Override
    public void addPersonToTag(int personId1, int personId2, int tagId) throws
            PersonIdNotFoundException, RelationNotFoundException,
            TagIdNotFoundException, EqualPersonIdException {
        if (!containsPerson(personId1)) {
            throw new PersonIdNotFoundException(personId1);
        }
        if (!containsPerson(personId2)) {
            throw new PersonIdNotFoundException(personId2);
        }
        if (personId1 == personId2) {
            throw new EqualPersonIdException(personId1);
        }
        if (!getPerson(personId2).isLinked(getPerson(personId1))) {
            throw new RelationNotFoundException(personId1, personId2);
        }
        if (!getPerson(personId2).containsTag(tagId)) {
            throw new TagIdNotFoundException(tagId);
        }
        if (getPerson(personId2).getTag(tagId).hasPerson(getPerson(personId1))) {
            throw new EqualPersonIdException(personId1);
        }
        if (getPerson(personId2).getTag(tagId).getSize() <= 999) {
            ((Tag) getPerson(personId2).getTag(tagId)).addPerson(getPerson(personId1));
        }
    }

    @Override
    public int queryTagAgeVar(int personId, int tagId) throws PersonIdNotFoundException,
            TagIdNotFoundException {
        if (!containsPerson(personId)) {
            throw new PersonIdNotFoundException(personId);
        }
        if (!getPerson(personId).containsTag(tagId)) {
            throw new TagIdNotFoundException(tagId);
        }
        return getPerson(personId).getTag(tagId).getAgeVar();
    }

    @Override
    public void delPersonFromTag(int personId1, int personId2, int tagId) throws
            PersonIdNotFoundException, TagIdNotFoundException {
        if (!containsPerson(personId1)) {
            throw new PersonIdNotFoundException(personId1);
        }
        if (!containsPerson(personId2)) {
            throw new PersonIdNotFoundException(personId2);
        }
        if (!getPerson(personId2).containsTag(tagId)) {
            throw new TagIdNotFoundException(tagId);
        }
        if (!getPerson(personId2).getTag(tagId).hasPerson(getPerson(personId1))) {
            throw new PersonIdNotFoundException(personId1);
        }
        getPerson(personId2).getTag(tagId).delPerson(getPerson(personId1));
    }

    @Override
    public void delTag(int personId, int tagId) throws PersonIdNotFoundException,
            TagIdNotFoundException {
        if (!containsPerson(personId)) {
            throw new PersonIdNotFoundException(personId);
        }
        if (!getPerson(personId).containsTag(tagId)) {
            throw new TagIdNotFoundException(tagId);
        }
        ((Person) getPerson(personId)).delTag(tagId);
    }

    @Override
    public int queryBestAcquaintance(int id) throws PersonIdNotFoundException,
            AcquaintanceNotFoundException {
        if (!containsPerson(id)) {
            throw new PersonIdNotFoundException(id);
        }
        if (((Person) getPerson(id)).getAcquaintance().isEmpty()) {
            throw new AcquaintanceNotFoundException(id);
        }
        return ((Person) getPerson(id)).getBestAcquaintanceId();
    }

    /*--------------------------------------------------------------*/

    public PersonInterface [] getPersons() {
        return persons.values().toArray(new PersonInterface[0]);
    }
}
