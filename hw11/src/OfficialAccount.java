import com.oocourse.spec3.main.OfficialAccountInterface;
import com.oocourse.spec3.main.PersonInterface;

import java.util.HashMap;
import java.util.HashSet;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Collections;

public class OfficialAccount implements OfficialAccountInterface {
    private int ownerId;
    private int id;
    private String name;
    private HashMap<Integer, PersonInterface> followers; // key: person id, value: person object
    // key: person id, value: this person's contribution count
    private HashMap<Integer, Integer> contributions;
    private HashSet<Integer> articles; // article ids
    // key: contribution count, value: person ids
    private TreeMap<Integer, TreeSet<Integer>> contributionToIds;

    public OfficialAccount(int ownerId, int id, String name) {
        this.ownerId = ownerId;
        this.id = id;
        this.name = name;
        this.followers = new HashMap<>();
        this.contributions = new HashMap<>();
        this.articles = new HashSet<>();
        this.contributionToIds = new TreeMap<>(Collections.reverseOrder());
    }

    @Override
    public int getOwnerId() {
        return this.ownerId;
    }

    @Override
    public void addFollower(PersonInterface person) {
        if (!containsFollower(person)) {
            followers.put(person.getId(), person);
            contributions.put(person.getId(), 0);
            contributionToIds.computeIfAbsent(0, k -> new TreeSet<>()).add(person.getId());
        }
    }

    @Override
    public boolean containsFollower(PersonInterface person) {
        return followers.containsKey(person.getId());
    }

    @Override
    public void addArticle(PersonInterface person, int id) {
        if (!containsArticle(id) && containsFollower(person)) {
            articles.add(id);
            int oldContrib = contributions.get(person.getId());
            contributions.put(person.getId(), oldContrib + 1);
            contributionToIds.get(oldContrib).remove(person.getId());
            if (contributionToIds.get(oldContrib).isEmpty()) {
                contributionToIds.remove(oldContrib);
            }
            contributionToIds.computeIfAbsent(oldContrib + 1, k -> new TreeSet<>()).
                    add(person.getId());
        }
    }

    @Override
    public boolean containsArticle(int id) {
        return articles.contains(id);
    }

    @Override
    public void removeArticle(int id) {
        if (containsArticle(id)) {
            articles.remove(id);
        }
    }

    @Override
    public int getBestContributor() {
        if (contributionToIds.isEmpty()) {
            return Integer.MAX_VALUE;
        }
        return contributionToIds.firstEntry().getValue().first();
    }

    /*---------------------------------------------------------------*/

    public void decreaseContribution(int personId) {
        if (contributions.containsKey(personId)) {
            int oldContrib = contributions.get(personId);
            contributions.put(personId, oldContrib - 1);
            contributionToIds.get(oldContrib).remove(personId);
            if (contributionToIds.get(oldContrib).isEmpty()) {
                contributionToIds.remove(oldContrib);
            }
            contributionToIds.computeIfAbsent(oldContrib - 1, k -> new TreeSet<>()).add(personId);
        }
    }

    public HashMap<Integer, PersonInterface> getFollowers() {
        return followers;
    }

    public HashSet<Integer> getArticles() {
        return articles;
    }
}
