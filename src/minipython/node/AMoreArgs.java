/* This file was generated by SableCC (http://www.sablecc.org/). */

package minipython.node;

import java.util.*;
import minipython.analysis.*;

public final class AMoreArgs extends PMoreArgs
{
    private TId _id_;
    private PAssignValue _assignValue_;

    public AMoreArgs()
    {
    }

    public AMoreArgs(
        TId _id_,
        PAssignValue _assignValue_)
    {
        setId(_id_);

        setAssignValue(_assignValue_);

    }
    public Object clone()
    {
        return new AMoreArgs(
            (TId) cloneNode(_id_),
            (PAssignValue) cloneNode(_assignValue_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAMoreArgs(this);
    }

    public TId getId()
    {
        return _id_;
    }

    public void setId(TId node)
    {
        if(_id_ != null)
        {
            _id_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        _id_ = node;
    }

    public PAssignValue getAssignValue()
    {
        return _assignValue_;
    }

    public void setAssignValue(PAssignValue node)
    {
        if(_assignValue_ != null)
        {
            _assignValue_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        _assignValue_ = node;
    }

    public String toString()
    {
        return ""
            + toString(_id_)
            + toString(_assignValue_);
    }

    void removeChild(Node child)
    {
        if(_id_ == child)
        {
            _id_ = null;
            return;
        }

        if(_assignValue_ == child)
        {
            _assignValue_ = null;
            return;
        }

    }

    void replaceChild(Node oldChild, Node newChild)
    {
        if(_id_ == oldChild)
        {
            setId((TId) newChild);
            return;
        }

        if(_assignValue_ == oldChild)
        {
            setAssignValue((PAssignValue) newChild);
            return;
        }

    }
}
