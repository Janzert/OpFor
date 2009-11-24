
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

    T get(double timeout=0)
    {
        synchronized (mutex)
        {
            if (qhead is null && timeout != 0)
            {
                if (timeout > 0)
                {
                    cnd.wait(timeout);
                } else {
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
            cnd.notify();
        }
    }
}

