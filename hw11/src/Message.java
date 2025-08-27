import com.oocourse.spec3.main.MessageInterface;
import com.oocourse.spec3.main.PersonInterface;
import com.oocourse.spec3.main.TagInterface;

public class Message implements MessageInterface {
    private int id;
    private int socialValue;
    private int type;
    private PersonInterface person1;
    private PersonInterface person2;
    private TagInterface tag;

    public Message(int messageId, int messageSocialValue, PersonInterface messagePerson1,
                   PersonInterface messagePerson2) {
        this.type = 0; // person to person message
        this.tag = null;
        this.id = messageId;
        this.socialValue = messageSocialValue;
        this.person1 = messagePerson1;
        this.person2 = messagePerson2;
    }

    public Message(int messageId, int messageSocialValue, PersonInterface messagePerson1,
                   TagInterface messageTag) {
        this.type = 1; // person to tag message
        this.person2 = null;
        this.id = messageId;
        this.socialValue = messageSocialValue;
        this.person1 = messagePerson1;
        this.tag = messageTag;
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
        return this.socialValue;
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
