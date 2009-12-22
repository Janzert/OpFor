
import tango.core.sync.Condition;
import tango.core.sync.Mutex;

class Queue(T)
{
    struct QMsg
    {
        QMsg* next;
        T msg;
    }
    QMsg* qhead = null;
    QMsg* qtail = null;
    QMsg* qbuf = null;

    Mutex mutex;
    Condition cnd;

    this()
    {
        mutex = new Mutex();
        cnd = new Condition(mutex);
    }

    void clear()
    {
        synchronized (mutex)
        {
            while (qhead !is null)
            {
                QMsg* qmsg = qhead;
                qhead = qhead.next;
                qmsg.msg = null;
                qmsg.next = qbuf;
                qbuf = qmsg;
            }
            qtail = null;
        }
    }

    bool has_item()
    {
        synchronized (mutex)
        {
            if (qhead !is null)
                return true;
            return false;
        }
    }

    // 0 timeout does not wait, a negative timeout will wait forever
    T get(double timeout=0)
    {
        synchronized (mutex)
        {
            if (qhead is null && timeout != 0)
            {
                if (timeout > 0)
                {
                    cnd.wait(timeout);
                } else { // timeout must be negative
                    cnd.wait();
                }
            }

            if (qhead !is null)
            {
                QMsg* qmsg = qhead;
                qhead = qhead.next;
                if (qhead is null)
                {
                    assert(qtail is qmsg);
                    qtail = null;
                }
                T msg = qmsg.msg;
                qmsg.msg = null;
                qmsg.next = qbuf;
                qbuf = qmsg;

                return msg;
            }
            return null;
        }
    }

    void set(T msg)
    {
        synchronized (mutex)
        {
            QMsg* qmsg;
            if (qbuf !is null)
            {
                qmsg = qbuf;
                qbuf = qmsg.next;
            } else {
                qmsg = new QMsg();
            }

            qmsg.msg = msg;
            qmsg.next = null;

            if (qtail !is null)
            {
                qtail.next = qmsg;
                qtail = qmsg;
            } else {
                qhead = qmsg;
                qtail = qmsg;
            }
        }
        cnd.notify();
    }
}

