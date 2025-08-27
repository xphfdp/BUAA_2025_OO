import com.oocourse.spec3.main.ForwardMessageInterface;
import com.oocourse.spec3.main.MessageInterface;
import com.oocourse.spec3.main.PersonInterface;
import com.oocourse.spec3.main.TagInterface;

import static java.lang.Math.abs;

public class ForwardMessage implements ForwardMessageInterface {
    private int id;
    private int articleId;
    private int type;
    private PersonInterface person1;
    private PersonInterface person2;
    private TagInterface tag;

    public ForwardMessage(int messageId, int article, PersonInterface messagePerson1,
                          PersonInterface messagePerson2) {
        this.type = 0;
        this.tag = null;
        this.id = messageId;
        this.person1 = messagePerson1;
        this.person2 = messagePerson2;
        this.articleId = article;
    }

    public ForwardMessage(int messageId, int article, PersonInterface messagePerson1,
                          TagInterface messageTag) {
        this.type = 1;
        this.person2 = null;
        this.id = messageId;
        this.person1 = messagePerson1;
        this.tag = messageTag;
        this.articleId = article;
    }

    @Override
    public int getArticleId() {
        return this.articleId;
    }

    @Override
    public int getType() {
        return this.type;
    }

    @Override
    public int getId() {
        return this.id;
    }

    @Override
    public int getSocialValue() {
        return abs(this.articleId) % 200;
    }

    @Override
    public PersonInterface getPerson1() {
        return this.person1;
    }

    @Override
    public PersonInterface getPerson2() {
        return this.person2;
    }

    @Override
    public TagInterface getTag() {
        return this.tag;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj != null && obj instanceof MessageInterface) {
            return ((MessageInterface) obj).getId() == id;
        } else {
            return false;
        }
    }
}
