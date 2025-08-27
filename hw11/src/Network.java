import com.oocourse.spec3.exceptions.EqualPersonIdException;
import com.oocourse.spec3.exceptions.EqualRelationException;
import com.oocourse.spec3.exceptions.PersonIdNotFoundException;
import com.oocourse.spec3.exceptions.RelationNotFoundException;
import com.oocourse.spec3.exceptions.EqualTagIdException;
import com.oocourse.spec3.exceptions.TagIdNotFoundException;
import com.oocourse.spec3.exceptions.AcquaintanceNotFoundException;
import com.oocourse.spec3.exceptions.PathNotFoundException;
import com.oocourse.spec3.exceptions.OfficialAccountIdNotFoundException;
import com.oocourse.spec3.exceptions.ArticleIdNotFoundException;
import com.oocourse.spec3.exceptions.EqualOfficialAccountIdException;
import com.oocourse.spec3.exceptions.DeleteArticlePermissionDeniedException;
import com.oocourse.spec3.exceptions.DeleteOfficialAccountPermissionDeniedException;
import com.oocourse.spec3.exceptions.EqualArticleIdException;
import com.oocourse.spec3.exceptions.ContributePermissionDeniedException;
import com.oocourse.spec3.exceptions.EqualMessageIdException;
import com.oocourse.spec3.exceptions.EmojiIdNotFoundException;
import com.oocourse.spec3.exceptions.MessageIdNotFoundException;
import com.oocourse.spec3.exceptions.EqualEmojiIdException;
import com.oocourse.spec3.main.MessageInterface;
import com.oocourse.spec3.main.NetworkInterface;
import com.oocourse.spec3.main.OfficialAccountInterface;
import com.oocourse.spec3.main.PersonInterface;
import com.oocourse.spec3.main.TagInterface;
import com.oocourse.spec3.main.EmojiMessageInterface;
import com.oocourse.spec3.main.ForwardMessageInterface;
import com.oocourse.spec3.main.RedEnvelopeMessageInterface;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;

public class Network implements NetworkInterface {
    private HashMap<Integer, PersonInterface> persons;
    private int tripleSum;
    private DisjointSet disjointSet;
    private boolean disjointSetNeedReset;
    private HashMap<Integer, OfficialAccountInterface> accounts; // key: accountId, value: account
    private HashSet<Integer> articles; // articleId
    private HashMap<Integer, Integer> articleContributors; // key: articleId, value: contributorId
    private HashMap<Integer, MessageInterface> messages; // key: messageId, value: message
    private HashMap<Integer, Integer> emojiMap; // key:emojiIdd, value:heat
    private int[] emojiHeatList;

    public Network() {
        this.persons = new HashMap<>();
        this.tripleSum = 0;
        this.disjointSet = new DisjointSet();
        this.disjointSetNeedReset = false;
        this.accounts = new HashMap<>();
        this.articles = new HashSet<>();
        this.articleContributors = new HashMap<>();
        this.messages = new HashMap<>();
        this.emojiMap = new HashMap<>();
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
        persons.values().forEach(p -> ((Person) p).updateTagValueSum(id1, id2, value));
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
            persons.values().forEach(p -> ((Person) p).updateTagValueSum(id1, id2, value));
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
            persons.values().forEach(p -> ((Person) p).updateTagValueSum(id1, id2, -oldValue));
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

    @Override
    public int queryTagValueSum(int personId, int tagId) throws PersonIdNotFoundException,
            TagIdNotFoundException {
        if (!containsPerson(personId)) {
            throw new PersonIdNotFoundException(personId);
        }
        if (!getPerson(personId).containsTag(tagId)) {
            throw new TagIdNotFoundException(tagId);
        }
        return getPerson(personId).getTag(tagId).getValueSum();
    }

    @Override
    public int queryCoupleSum() {
        int coupleSum = 0;
        for (PersonInterface person : this.persons.values()) {
            Person person1 = ((Person) person);
            if (!person1.isAcquaintanceEmpty() && ((Person) this.persons.
                    get(person1.getBestAcquaintanceId())).getBestAcquaintanceId() ==
                    person1.getId()) {
                coupleSum++;
            }
        }
        return coupleSum / 2;
    }

    @Override
    public int queryShortestPath(int id1, int id2) throws PersonIdNotFoundException,
            PathNotFoundException {
        if (!containsPerson(id1)) {
            throw new PersonIdNotFoundException(id1);
        }
        if (!containsPerson(id2)) {
            throw new PersonIdNotFoundException(id2);
        }
        if (!isCircle(id1, id2)) {
            throw new PathNotFoundException(id1, id2);
        }
        if (id1 == id2) {
            return 0;
        }
        HashMap<Integer, Integer> dist = new HashMap<>();
        Queue<Integer> queue = new LinkedList<>();
        dist.put(id1, 0);
        queue.offer(id1);
        while (!queue.isEmpty()) {
            int current = queue.poll();
            PersonInterface person = getPerson(current);
            for (PersonInterface neighbor : ((Person) person).getAcquaintance().values()) {
                int neighborId = neighbor.getId();
                if (!dist.containsKey(neighborId)) {
                    dist.put(neighborId, dist.get(current) + 1);
                    queue.offer(neighborId);
                    if (neighborId == id2) {
                        return dist.get(neighborId);
                    }
                }
            }
        }
        throw new PathNotFoundException(id1, id2);
    }

    @Override
    public boolean containsAccount(int id) {
        return accounts.containsKey(id);
    }

    @Override
    public void createOfficialAccount(int personId, int accountId, String name) throws
            PersonIdNotFoundException, EqualOfficialAccountIdException {
        if (!containsPerson(personId)) {
            throw new PersonIdNotFoundException(personId);
        }
        if (containsAccount(accountId)) {
            throw new EqualOfficialAccountIdException(accountId);
        }
        OfficialAccount account = new OfficialAccount(personId, accountId, name);
        account.addFollower(persons.get(personId));
        accounts.put(accountId, account);
    }

    @Override
    public void deleteOfficialAccount(int personId, int accountId) throws
            PersonIdNotFoundException, OfficialAccountIdNotFoundException,
            DeleteOfficialAccountPermissionDeniedException {
        if (!containsPerson(personId)) {
            throw new PersonIdNotFoundException(personId);
        }
        if (!containsAccount(accountId)) {
            throw new OfficialAccountIdNotFoundException(accountId);
        }
        if (accounts.get(accountId).getOwnerId() != personId) {
            throw new DeleteOfficialAccountPermissionDeniedException(personId, accountId);
        }
        accounts.remove(accountId);
    }

    @Override
    public boolean containsArticle(int id) {
        return articles.contains(id);
    }

    @Override
    public void contributeArticle(int personId, int accountId, int articleId) throws
            PersonIdNotFoundException, OfficialAccountIdNotFoundException,
            EqualArticleIdException, ContributePermissionDeniedException {
        if (!containsPerson(personId)) {
            throw new PersonIdNotFoundException(personId);
        }
        if (!containsAccount(accountId)) {
            throw new OfficialAccountIdNotFoundException(accountId);
        }
        if (containsArticle(articleId)) {
            throw new EqualArticleIdException(articleId);
        }
        if (!accounts.get(accountId).containsFollower(getPerson(personId))) {
            throw new ContributePermissionDeniedException(personId, articleId);
        }
        articles.add(articleId);
        accounts.get(accountId).addArticle(getPerson(personId), articleId);
        articleContributors.put(articleId, personId);
        for (PersonInterface follower : ((OfficialAccount) accounts.get(accountId)).
                getFollowers().values()) {
            ((Person) follower).addReceivedArticle(articleId);
        }
    }

    @Override
    public void deleteArticle(int personId, int accountId, int articleId) throws
            PersonIdNotFoundException, OfficialAccountIdNotFoundException,
            ArticleIdNotFoundException, DeleteArticlePermissionDeniedException {
        if (!containsPerson(personId)) {
            throw new PersonIdNotFoundException(personId);
        }
        if (!containsAccount(accountId)) {
            throw new OfficialAccountIdNotFoundException(accountId);
        }
        if (!accounts.get(accountId).containsArticle(articleId)) {
            throw new ArticleIdNotFoundException(articleId);
        }
        if (accounts.get(accountId).getOwnerId() != personId) {
            throw new DeleteArticlePermissionDeniedException(personId, articleId);
        }
        accounts.get(accountId).removeArticle(articleId);
        int contributorId = articleContributors.get(articleId);
        ((OfficialAccount) accounts.get(accountId)).decreaseContribution(contributorId);
        for (PersonInterface follower : ((OfficialAccount) accounts.get(accountId)).
                getFollowers().values()) {
            ((Person) follower).removeReceivedArticle(articleId);
        }
    }

    @Override
    public void followOfficialAccount(int personId, int accountId) throws
            PersonIdNotFoundException, OfficialAccountIdNotFoundException,
            EqualPersonIdException {
        if (!containsPerson(personId)) {
            throw new PersonIdNotFoundException(personId);
        }
        if (!containsAccount(accountId)) {
            throw new OfficialAccountIdNotFoundException(accountId);
        }
        if (accounts.get(accountId).containsFollower(getPerson(personId))) {
            throw new EqualPersonIdException(personId);
        }
        accounts.get(accountId).addFollower(getPerson(personId));
    }

    @Override
    public int queryBestContributor(int id) throws OfficialAccountIdNotFoundException {
        if (!containsAccount(id)) {
            throw new OfficialAccountIdNotFoundException(id);
        }
        return accounts.get(id).getBestContributor();
    }

    @Override
    public LinkedList<Integer> queryReceivedArticles(int id) throws PersonIdNotFoundException {
        if (!containsPerson(id)) {
            throw new PersonIdNotFoundException(id);
        }
        return ((Person) persons.get(id)).queryReceivedArticles();
    }

    @Override
    public boolean containsMessage(int id) {
        return messages.containsKey(id);
    }

    @Override
    public void addMessage(MessageInterface message) throws EqualMessageIdException,
            EmojiIdNotFoundException, EqualPersonIdException, ArticleIdNotFoundException {
        if (containsMessage(message.getId())) {
            throw new EqualMessageIdException(message.getId());
        }
        if (message instanceof EmojiMessageInterface &&
                !containsEmojiId(((EmojiMessageInterface) message).getEmojiId())) {
            throw new EmojiIdNotFoundException(((EmojiMessageInterface) message).getEmojiId());
        }
        if (message instanceof ForwardMessageInterface &&
                !containsArticle(((ForwardMessageInterface) message).getArticleId())) {
            ForwardMessageInterface forwardMessage = (ForwardMessageInterface) message;
            throw new ArticleIdNotFoundException(forwardMessage.getArticleId());
        }
        if (message instanceof ForwardMessageInterface &&
                containsArticle(((ForwardMessageInterface) message).getArticleId())
                && !(message.getPerson1().getReceivedArticles().
                contains(((ForwardMessageInterface) message).getArticleId()))) {
            ForwardMessageInterface forwardMessage = (ForwardMessageInterface) message;
            throw new ArticleIdNotFoundException(forwardMessage.getArticleId());
        }
        if (message.getType() == 0 && message.getPerson1().equals(message.getPerson2())) {
            throw new EqualPersonIdException(message.getPerson1().getId());
        }
        messages.put(message.getId(), message);
    }

    @Override
    public MessageInterface getMessage(int id) {
        if (containsMessage(id)) {
            return messages.get(id);
        } else {
            return null;
        }
    }

    @Override
    public void sendMessage(int id) throws RelationNotFoundException,
            MessageIdNotFoundException, TagIdNotFoundException {
        if (!containsMessage(id)) {
            throw new MessageIdNotFoundException(id);
        }
        MessageInterface message = getMessage(id);
        if (message.getType() == 0 && !message.getPerson1().isLinked(message.getPerson2())) {
            throw new RelationNotFoundException(message.getPerson1().getId(),
                    message.getPerson2().getId());
        }
        if (message.getType() == 1 && !message.getPerson1().containsTag(message.getTag().getId())) {
            throw new TagIdNotFoundException(message.getTag().getId());
        }
        if (message.getType() == 0) {
            handleType0Message(message);
        } else {
            handleType1Message(message);
        }
        messages.remove(id);
    }

    @Override
    public LinkedList<MessageInterface> queryReceivedMessages(int id)
            throws PersonIdNotFoundException {
        if (!containsPerson(id)) {
            throw new PersonIdNotFoundException(id);
        }
        return ((Person) getPerson(id)).getReceivedMessages();
    }

    @Override
    public boolean containsEmojiId(int id) {
        return emojiMap.containsKey(id);
    }

    @Override
    public void storeEmojiId(int id) throws EqualEmojiIdException {
        if (containsEmojiId(id)) {
            throw new EqualEmojiIdException(id);
        }
        emojiMap.put(id, 0);

    }

    @Override
    public int querySocialValue(int id) throws PersonIdNotFoundException {
        if (!containsPerson(id)) {
            throw new PersonIdNotFoundException(id);
        }
        return getPerson(id).getSocialValue();
    }

    @Override
    public int queryMoney(int id) throws PersonIdNotFoundException {
        if (!containsPerson(id)) {
            throw new PersonIdNotFoundException(id);
        }
        return getPerson(id).getMoney();
    }

    @Override
    public int queryPopularity(int id) throws EmojiIdNotFoundException {
        if (!containsEmojiId(id)) {
            throw new EmojiIdNotFoundException(id);
        }
        return emojiMap.get(id);
    }

    @Override
    public int deleteColdEmoji(int limit) {
        emojiMap.entrySet().removeIf(entry -> entry.getValue() < limit);
        messages.entrySet().removeIf(entry -> entry.getValue() instanceof
                EmojiMessageInterface && !containsEmojiId(((EmojiMessageInterface)
                entry.getValue()).getEmojiId()));
        return emojiMap.size();
    }

    /*--------------------------helper methods--------------------------------*/

    private void handleType0Message(MessageInterface message) {
        PersonInterface person1 = message.getPerson1();
        PersonInterface person2 = message.getPerson2();
        if (!person1.equals(person2)) {
            person1.addSocialValue(message.getSocialValue());
            person2.addSocialValue(message.getSocialValue());
            if (message instanceof RedEnvelopeMessageInterface) {
                RedEnvelopeMessageInterface rem = (RedEnvelopeMessageInterface) message;
                person1.addMoney(-rem.getMoney());
                person2.addMoney(rem.getMoney());
            } else if (message instanceof ForwardMessageInterface) {
                ForwardMessageInterface forwardMessage = (ForwardMessageInterface) message;
                ((Person) person2).addReceivedArticle(forwardMessage.getArticleId());
            } else if (message instanceof EmojiMessageInterface) {
                EmojiMessageInterface emojiMessage = (EmojiMessageInterface) message;
                if (containsEmojiId(emojiMessage.getEmojiId())) {
                    emojiMap.put(emojiMessage.getEmojiId(),
                            emojiMap.get(emojiMessage.getEmojiId()) + 1);
                }
            }
        }
        ((Person) person2).addMessageOnHead(message);
    }

    private void handleType1Message(MessageInterface message) {
        PersonInterface person1 = message.getPerson1();
        TagInterface tag = message.getTag();
        person1.addSocialValue(message.getSocialValue());
        HashMap<Integer, PersonInterface> tagPersons = ((Tag) tag).getPersons();
        for (PersonInterface person : tagPersons.values()) {
            person.addSocialValue(message.getSocialValue());
            if (message instanceof RedEnvelopeMessageInterface && tag.getSize() > 0) {
                RedEnvelopeMessageInterface rem = (RedEnvelopeMessageInterface) message;
                int moneyPerPerson = rem.getMoney() / tag.getSize();
                person.addMoney(moneyPerPerson);
            } else if (message instanceof ForwardMessageInterface && tag.getSize() > 0) {
                ForwardMessageInterface forwardMessage = (ForwardMessageInterface) message;
                ((Person) person).addReceivedArticle(forwardMessage.getArticleId());
            }
            ((Person) person).addMessageOnHead(message);
        }
        if (message instanceof RedEnvelopeMessageInterface && tag.getSize() > 0) {
            RedEnvelopeMessageInterface rem = (RedEnvelopeMessageInterface) message;
            int moneyPerPerson = rem.getMoney() / tag.getSize();
            person1.addMoney(-moneyPerPerson * tag.getSize());
        }
        if (message instanceof EmojiMessageInterface) {
            EmojiMessageInterface emojiMessage = (EmojiMessageInterface) message;
            if (containsEmojiId(emojiMessage.getEmojiId())) {
                emojiMap.put(emojiMessage.getEmojiId(),
                        emojiMap.get(emojiMessage.getEmojiId()) + 1);
            }
        }
    }

    /*--------------------------for test only---------------------------------*/

    public PersonInterface[] getPersons() {
        return persons.values().toArray(new PersonInterface[0]);
    }

    public MessageInterface[] getMessages() {
        int size = messages.size();
        MessageInterface[] array = new MessageInterface[size];
        int iter = 0;
        for (MessageInterface message : messages.values()) {
            array[iter++] = message;
        }
        return array;
    }

    public int[] getEmojiIdList() {
        int size = emojiMap.size();
        int[] array = new int[size];
        emojiHeatList = new int[size];
        int iter = 0;
        for (int emojiId : emojiMap.keySet()) {
            array[iter] = emojiId;
            emojiHeatList[iter] = emojiMap.get(emojiId);
            iter++;
        }
        return array;
    }

    public int[] getEmojiHeatList() {
        return emojiHeatList;
    }
}
