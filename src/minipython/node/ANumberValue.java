/* This file was generated by SableCC (http://www.sablecc.org/). */

package minipython.node;

import java.util.*;
import minipython.analysis.*;

public final class ANumberValue extends PValue
{
    private PNumber _number_;

    public ANumberValue()
    {
    }

    public ANumberValue(
        PNumber _number_)
    {
        setNumber(_number_);

    }
    public Object clone()
    {
        return new ANumberValue(
            (PNumber) cloneNode(_number_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseANumberValue(this);
    }

    public PNumber getNumber()
    {
        return _number_;
    }

    public void setNumber(PNumber node)
    {
        if(_number_ != null)
        {
            _number_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        _number_ = node;
    }

    public String toString()
    {
        return ""
            + toString(_number_);
    }

    void removeChild(Node child)
    {
        if(_number_ == child)
        {
            _number_ = null;
            return;
        }

    }

    void replaceChild(Node oldChild, Node newChild)
    {
        if(_number_ == oldChild)
        {
            setNumber((PNumber) newChild);
            return;
        }

    }
}
