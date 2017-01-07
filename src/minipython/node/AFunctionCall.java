/* This file was generated by SableCC (http://www.sablecc.org/). */

package minipython.node;

import java.util.*;
import minipython.analysis.*;

public final class AFunctionCall extends PFunctionCall
{
    private TId _id_;
    private PArgList _argList_;

    public AFunctionCall()
    {
    }

    public AFunctionCall(
        TId _id_,
        PArgList _argList_)
    {
        setId(_id_);

        setArgList(_argList_);

    }
    public Object clone()
    {
        return new AFunctionCall(
            (TId) cloneNode(_id_),
            (PArgList) cloneNode(_argList_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAFunctionCall(this);
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

    public PArgList getArgList()
    {
        return _argList_;
    }

    public void setArgList(PArgList node)
    {
        if(_argList_ != null)
        {
            _argList_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        _argList_ = node;
    }

    public String toString()
    {
        return ""
            + toString(_id_)
            + toString(_argList_);
    }

    void removeChild(Node child)
    {
        if(_id_ == child)
        {
            _id_ = null;
            return;
        }

        if(_argList_ == child)
        {
            _argList_ = null;
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

        if(_argList_ == oldChild)
        {
            setArgList((PArgList) newChild);
            return;
        }

    }
}
