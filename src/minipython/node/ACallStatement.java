/* This file was generated by SableCC (http://www.sablecc.org/). */

package minipython.node;

import java.util.*;
import minipython.analysis.*;

public final class ACallStatement extends PStatement
{
    private PFunctionCall _functionCall_;

    public ACallStatement()
    {
    }

    public ACallStatement(
        PFunctionCall _functionCall_)
    {
        setFunctionCall(_functionCall_);

    }
    public Object clone()
    {
        return new ACallStatement(
            (PFunctionCall) cloneNode(_functionCall_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseACallStatement(this);
    }

    public PFunctionCall getFunctionCall()
    {
        return _functionCall_;
    }

    public void setFunctionCall(PFunctionCall node)
    {
        if(_functionCall_ != null)
        {
            _functionCall_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        _functionCall_ = node;
    }

    public String toString()
    {
        return ""
            + toString(_functionCall_);
    }

    void removeChild(Node child)
    {
        if(_functionCall_ == child)
        {
            _functionCall_ = null;
            return;
        }

    }

    void replaceChild(Node oldChild, Node newChild)
    {
        if(_functionCall_ == oldChild)
        {
            setFunctionCall((PFunctionCall) newChild);
            return;
        }

    }
}
