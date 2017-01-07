/* This file was generated by SableCC (http://www.sablecc.org/). */

package minipython.analysis;

import java.util.*;
import minipython.node.*;

public class DepthFirstAdapter extends AnalysisAdapter
{
    public void inStart(Start node)
    {
        defaultIn(node);
    }

    public void outStart(Start node)
    {
        defaultOut(node);
    }

    public void defaultIn(Node node)
    {
    }

    public void defaultOut(Node node)
    {
    }

    public void caseStart(Start node)
    {
        inStart(node);
        node.getPGoal().apply(this);
        node.getEOF().apply(this);
        outStart(node);
    }

    public void inACmdsGoal(ACmdsGoal node)
    {
        defaultIn(node);
    }

    public void outACmdsGoal(ACmdsGoal node)
    {
        defaultOut(node);
    }

    public void caseACmdsGoal(ACmdsGoal node)
    {
        inACmdsGoal(node);
        {
            Object temp[] = node.getCommands().toArray();
            for(int i = 0; i < temp.length; i++)
            {
                ((PCommands) temp[i]).apply(this);
            }
        }
        outACmdsGoal(node);
    }

    public void inAFuncCommands(AFuncCommands node)
    {
        defaultIn(node);
    }

    public void outAFuncCommands(AFuncCommands node)
    {
        defaultOut(node);
    }

    public void caseAFuncCommands(AFuncCommands node)
    {
        inAFuncCommands(node);
        if(node.getFunction() != null)
        {
            node.getFunction().apply(this);
        }
        outAFuncCommands(node);
    }

    public void inAStatementCommands(AStatementCommands node)
    {
        defaultIn(node);
    }

    public void outAStatementCommands(AStatementCommands node)
    {
        defaultOut(node);
    }

    public void caseAStatementCommands(AStatementCommands node)
    {
        inAStatementCommands(node);
        if(node.getStatement() != null)
        {
            node.getStatement().apply(this);
        }
        outAStatementCommands(node);
    }

    public void inAFuncFunction(AFuncFunction node)
    {
        defaultIn(node);
    }

    public void outAFuncFunction(AFuncFunction node)
    {
        defaultOut(node);
    }

    public void caseAFuncFunction(AFuncFunction node)
    {
        inAFuncFunction(node);
        if(node.getId() != null)
        {
            node.getId().apply(this);
        }
        if(node.getArgument() != null)
        {
            node.getArgument().apply(this);
        }
        if(node.getStatement() != null)
        {
            node.getStatement().apply(this);
        }
        outAFuncFunction(node);
    }

    public void inAArgArgument(AArgArgument node)
    {
        defaultIn(node);
    }

    public void outAArgArgument(AArgArgument node)
    {
        defaultOut(node);
    }

    public void caseAArgArgument(AArgArgument node)
    {
        inAArgArgument(node);
        if(node.getId() != null)
        {
            node.getId().apply(this);
        }
        if(node.getAssignValue() != null)
        {
            node.getAssignValue().apply(this);
        }
        {
            Object temp[] = node.getMoreArgs().toArray();
            for(int i = 0; i < temp.length; i++)
            {
                ((PMoreArgs) temp[i]).apply(this);
            }
        }
        outAArgArgument(node);
    }

    public void inAAssignValue(AAssignValue node)
    {
        defaultIn(node);
    }

    public void outAAssignValue(AAssignValue node)
    {
        defaultOut(node);
    }

    public void caseAAssignValue(AAssignValue node)
    {
        inAAssignValue(node);
        if(node.getValue() != null)
        {
            node.getValue().apply(this);
        }
        outAAssignValue(node);
    }

    public void inAMoreArgs(AMoreArgs node)
    {
        defaultIn(node);
    }

    public void outAMoreArgs(AMoreArgs node)
    {
        defaultOut(node);
    }

    public void caseAMoreArgs(AMoreArgs node)
    {
        inAMoreArgs(node);
        if(node.getId() != null)
        {
            node.getId().apply(this);
        }
        if(node.getAssignValue() != null)
        {
            node.getAssignValue().apply(this);
        }
        outAMoreArgs(node);
    }

    public void inAIfStatement(AIfStatement node)
    {
        defaultIn(node);
    }

    public void outAIfStatement(AIfStatement node)
    {
        defaultOut(node);
    }

    public void caseAIfStatement(AIfStatement node)
    {
        inAIfStatement(node);
        if(node.getComparison() != null)
        {
            node.getComparison().apply(this);
        }
        if(node.getStatement() != null)
        {
            node.getStatement().apply(this);
        }
        outAIfStatement(node);
    }

    public void inAWhileStatement(AWhileStatement node)
    {
        defaultIn(node);
    }

    public void outAWhileStatement(AWhileStatement node)
    {
        defaultOut(node);
    }

    public void caseAWhileStatement(AWhileStatement node)
    {
        inAWhileStatement(node);
        if(node.getComparison() != null)
        {
            node.getComparison().apply(this);
        }
        if(node.getStatement() != null)
        {
            node.getStatement().apply(this);
        }
        outAWhileStatement(node);
    }

    public void inAForStatement(AForStatement node)
    {
        defaultIn(node);
    }

    public void outAForStatement(AForStatement node)
    {
        defaultOut(node);
    }

    public void caseAForStatement(AForStatement node)
    {
        inAForStatement(node);
        if(node.getId1() != null)
        {
            node.getId1().apply(this);
        }
        if(node.getId2() != null)
        {
            node.getId2().apply(this);
        }
        if(node.getStatement() != null)
        {
            node.getStatement().apply(this);
        }
        outAForStatement(node);
    }

    public void inAReturnStatement(AReturnStatement node)
    {
        defaultIn(node);
    }

    public void outAReturnStatement(AReturnStatement node)
    {
        defaultOut(node);
    }

    public void caseAReturnStatement(AReturnStatement node)
    {
        inAReturnStatement(node);
        if(node.getExpression() != null)
        {
            node.getExpression().apply(this);
        }
        outAReturnStatement(node);
    }

    public void inAPrintStatement(APrintStatement node)
    {
        defaultIn(node);
    }

    public void outAPrintStatement(APrintStatement node)
    {
        defaultOut(node);
    }

    public void caseAPrintStatement(APrintStatement node)
    {
        inAPrintStatement(node);
        if(node.getExpression() != null)
        {
            node.getExpression().apply(this);
        }
        {
            Object temp[] = node.getMoreExp().toArray();
            for(int i = 0; i < temp.length; i++)
            {
                ((PMoreExp) temp[i]).apply(this);
            }
        }
        outAPrintStatement(node);
    }

    public void inAOpStatement(AOpStatement node)
    {
        defaultIn(node);
    }

    public void outAOpStatement(AOpStatement node)
    {
        defaultOut(node);
    }

    public void caseAOpStatement(AOpStatement node)
    {
        inAOpStatement(node);
        if(node.getId() != null)
        {
            node.getId().apply(this);
        }
        if(node.getExpression() != null)
        {
            node.getExpression().apply(this);
        }
        outAOpStatement(node);
    }

    public void inAListStatement(AListStatement node)
    {
        defaultIn(node);
    }

    public void outAListStatement(AListStatement node)
    {
        defaultOut(node);
    }

    public void caseAListStatement(AListStatement node)
    {
        inAListStatement(node);
        if(node.getId() != null)
        {
            node.getId().apply(this);
        }
        if(node.getExp1() != null)
        {
            node.getExp1().apply(this);
        }
        if(node.getExp2() != null)
        {
            node.getExp2().apply(this);
        }
        outAListStatement(node);
    }

    public void inACallStatement(ACallStatement node)
    {
        defaultIn(node);
    }

    public void outACallStatement(ACallStatement node)
    {
        defaultOut(node);
    }

    public void caseACallStatement(ACallStatement node)
    {
        inACallStatement(node);
        if(node.getFunctionCall() != null)
        {
            node.getFunctionCall().apply(this);
        }
        outACallStatement(node);
    }

    public void inAAddExpression(AAddExpression node)
    {
        defaultIn(node);
    }

    public void outAAddExpression(AAddExpression node)
    {
        defaultOut(node);
    }

    public void caseAAddExpression(AAddExpression node)
    {
        inAAddExpression(node);
        if(node.getLeft() != null)
        {
            node.getLeft().apply(this);
        }
        if(node.getRight() != null)
        {
            node.getRight().apply(this);
        }
        outAAddExpression(node);
    }

    public void inASubExpression(ASubExpression node)
    {
        defaultIn(node);
    }

    public void outASubExpression(ASubExpression node)
    {
        defaultOut(node);
    }

    public void caseASubExpression(ASubExpression node)
    {
        inASubExpression(node);
        if(node.getLeft() != null)
        {
            node.getLeft().apply(this);
        }
        if(node.getRight() != null)
        {
            node.getRight().apply(this);
        }
        outASubExpression(node);
    }

    public void inAMultiplicationExpression(AMultiplicationExpression node)
    {
        defaultIn(node);
    }

    public void outAMultiplicationExpression(AMultiplicationExpression node)
    {
        defaultOut(node);
    }

    public void caseAMultiplicationExpression(AMultiplicationExpression node)
    {
        inAMultiplicationExpression(node);
        if(node.getLeft() != null)
        {
            node.getLeft().apply(this);
        }
        if(node.getRight() != null)
        {
            node.getRight().apply(this);
        }
        outAMultiplicationExpression(node);
    }

    public void inADivisionExpression(ADivisionExpression node)
    {
        defaultIn(node);
    }

    public void outADivisionExpression(ADivisionExpression node)
    {
        defaultOut(node);
    }

    public void caseADivisionExpression(ADivisionExpression node)
    {
        inADivisionExpression(node);
        if(node.getLeft() != null)
        {
            node.getLeft().apply(this);
        }
        if(node.getRight() != null)
        {
            node.getRight().apply(this);
        }
        outADivisionExpression(node);
    }

    public void inAListExpression(AListExpression node)
    {
        defaultIn(node);
    }

    public void outAListExpression(AListExpression node)
    {
        defaultOut(node);
    }

    public void caseAListExpression(AListExpression node)
    {
        inAListExpression(node);
        if(node.getId() != null)
        {
            node.getId().apply(this);
        }
        if(node.getExpression() != null)
        {
            node.getExpression().apply(this);
        }
        outAListExpression(node);
    }

    public void inAMorevaluesExpression(AMorevaluesExpression node)
    {
        defaultIn(node);
    }

    public void outAMorevaluesExpression(AMorevaluesExpression node)
    {
        defaultOut(node);
    }

    public void caseAMorevaluesExpression(AMorevaluesExpression node)
    {
        inAMorevaluesExpression(node);
        if(node.getValue() != null)
        {
            node.getValue().apply(this);
        }
        {
            Object temp[] = node.getMoreValues().toArray();
            for(int i = 0; i < temp.length; i++)
            {
                ((PMoreValues) temp[i]).apply(this);
            }
        }
        outAMorevaluesExpression(node);
    }

    public void inAPrePlusPlusExpression(APrePlusPlusExpression node)
    {
        defaultIn(node);
    }

    public void outAPrePlusPlusExpression(APrePlusPlusExpression node)
    {
        defaultOut(node);
    }

    public void caseAPrePlusPlusExpression(APrePlusPlusExpression node)
    {
        inAPrePlusPlusExpression(node);
        if(node.getPrePostElements() != null)
        {
            node.getPrePostElements().apply(this);
        }
        outAPrePlusPlusExpression(node);
    }

    public void inAPreMinusMinusExpression(APreMinusMinusExpression node)
    {
        defaultIn(node);
    }

    public void outAPreMinusMinusExpression(APreMinusMinusExpression node)
    {
        defaultOut(node);
    }

    public void caseAPreMinusMinusExpression(APreMinusMinusExpression node)
    {
        inAPreMinusMinusExpression(node);
        if(node.getPrePostElements() != null)
        {
            node.getPrePostElements().apply(this);
        }
        outAPreMinusMinusExpression(node);
    }

    public void inAPostPlusPlusExpression(APostPlusPlusExpression node)
    {
        defaultIn(node);
    }

    public void outAPostPlusPlusExpression(APostPlusPlusExpression node)
    {
        defaultOut(node);
    }

    public void caseAPostPlusPlusExpression(APostPlusPlusExpression node)
    {
        inAPostPlusPlusExpression(node);
        if(node.getPrePostElements() != null)
        {
            node.getPrePostElements().apply(this);
        }
        outAPostPlusPlusExpression(node);
    }

    public void inAPostMinusMinusExpression(APostMinusMinusExpression node)
    {
        defaultIn(node);
    }

    public void outAPostMinusMinusExpression(APostMinusMinusExpression node)
    {
        defaultOut(node);
    }

    public void caseAPostMinusMinusExpression(APostMinusMinusExpression node)
    {
        inAPostMinusMinusExpression(node);
        if(node.getPrePostElements() != null)
        {
            node.getPrePostElements().apply(this);
        }
        outAPostMinusMinusExpression(node);
    }

    public void inAValueExpression(AValueExpression node)
    {
        defaultIn(node);
    }

    public void outAValueExpression(AValueExpression node)
    {
        defaultOut(node);
    }

    public void caseAValueExpression(AValueExpression node)
    {
        inAValueExpression(node);
        if(node.getValue() != null)
        {
            node.getValue().apply(this);
        }
        outAValueExpression(node);
    }

    public void inAIdExpression(AIdExpression node)
    {
        defaultIn(node);
    }

    public void outAIdExpression(AIdExpression node)
    {
        defaultOut(node);
    }

    public void caseAIdExpression(AIdExpression node)
    {
        inAIdExpression(node);
        if(node.getId() != null)
        {
            node.getId().apply(this);
        }
        outAIdExpression(node);
    }

    public void inAFuncExpression(AFuncExpression node)
    {
        defaultIn(node);
    }

    public void outAFuncExpression(AFuncExpression node)
    {
        defaultOut(node);
    }

    public void caseAFuncExpression(AFuncExpression node)
    {
        inAFuncExpression(node);
        if(node.getFunctionCall() != null)
        {
            node.getFunctionCall().apply(this);
        }
        outAFuncExpression(node);
    }

    public void inAParenthesisExpression(AParenthesisExpression node)
    {
        defaultIn(node);
    }

    public void outAParenthesisExpression(AParenthesisExpression node)
    {
        defaultOut(node);
    }

    public void caseAParenthesisExpression(AParenthesisExpression node)
    {
        inAParenthesisExpression(node);
        if(node.getExpression() != null)
        {
            node.getExpression().apply(this);
        }
        outAParenthesisExpression(node);
    }

    public void inAListPrePostElements(AListPrePostElements node)
    {
        defaultIn(node);
    }

    public void outAListPrePostElements(AListPrePostElements node)
    {
        defaultOut(node);
    }

    public void caseAListPrePostElements(AListPrePostElements node)
    {
        inAListPrePostElements(node);
        if(node.getId() != null)
        {
            node.getId().apply(this);
        }
        if(node.getExpression() != null)
        {
            node.getExpression().apply(this);
        }
        outAListPrePostElements(node);
    }

    public void inAIdPrePostElements(AIdPrePostElements node)
    {
        defaultIn(node);
    }

    public void outAIdPrePostElements(AIdPrePostElements node)
    {
        defaultOut(node);
    }

    public void caseAIdPrePostElements(AIdPrePostElements node)
    {
        inAIdPrePostElements(node);
        if(node.getId() != null)
        {
            node.getId().apply(this);
        }
        outAIdPrePostElements(node);
    }

    public void inAMoreValues(AMoreValues node)
    {
        defaultIn(node);
    }

    public void outAMoreValues(AMoreValues node)
    {
        defaultOut(node);
    }

    public void caseAMoreValues(AMoreValues node)
    {
        inAMoreValues(node);
        if(node.getValue() != null)
        {
            node.getValue().apply(this);
        }
        outAMoreValues(node);
    }

    public void inAGreatComparison(AGreatComparison node)
    {
        defaultIn(node);
    }

    public void outAGreatComparison(AGreatComparison node)
    {
        defaultOut(node);
    }

    public void caseAGreatComparison(AGreatComparison node)
    {
        inAGreatComparison(node);
        if(node.getExp1() != null)
        {
            node.getExp1().apply(this);
        }
        if(node.getExp2() != null)
        {
            node.getExp2().apply(this);
        }
        outAGreatComparison(node);
    }

    public void inALessComparison(ALessComparison node)
    {
        defaultIn(node);
    }

    public void outALessComparison(ALessComparison node)
    {
        defaultOut(node);
    }

    public void caseALessComparison(ALessComparison node)
    {
        inALessComparison(node);
        if(node.getExp1() != null)
        {
            node.getExp1().apply(this);
        }
        if(node.getExp2() != null)
        {
            node.getExp2().apply(this);
        }
        outALessComparison(node);
    }

    public void inAEqComparison(AEqComparison node)
    {
        defaultIn(node);
    }

    public void outAEqComparison(AEqComparison node)
    {
        defaultOut(node);
    }

    public void caseAEqComparison(AEqComparison node)
    {
        inAEqComparison(node);
        if(node.getExp1() != null)
        {
            node.getExp1().apply(this);
        }
        if(node.getExp2() != null)
        {
            node.getExp2().apply(this);
        }
        outAEqComparison(node);
    }

    public void inANoteqComparison(ANoteqComparison node)
    {
        defaultIn(node);
    }

    public void outANoteqComparison(ANoteqComparison node)
    {
        defaultOut(node);
    }

    public void caseANoteqComparison(ANoteqComparison node)
    {
        inANoteqComparison(node);
        if(node.getExp1() != null)
        {
            node.getExp1().apply(this);
        }
        if(node.getExp2() != null)
        {
            node.getExp2().apply(this);
        }
        outANoteqComparison(node);
    }

    public void inATrueComparison(ATrueComparison node)
    {
        defaultIn(node);
    }

    public void outATrueComparison(ATrueComparison node)
    {
        defaultOut(node);
    }

    public void caseATrueComparison(ATrueComparison node)
    {
        inATrueComparison(node);
        outATrueComparison(node);
    }

    public void inAFalseComparison(AFalseComparison node)
    {
        defaultIn(node);
    }

    public void outAFalseComparison(AFalseComparison node)
    {
        defaultOut(node);
    }

    public void caseAFalseComparison(AFalseComparison node)
    {
        inAFalseComparison(node);
        outAFalseComparison(node);
    }

    public void inAFunctionCall(AFunctionCall node)
    {
        defaultIn(node);
    }

    public void outAFunctionCall(AFunctionCall node)
    {
        defaultOut(node);
    }

    public void caseAFunctionCall(AFunctionCall node)
    {
        inAFunctionCall(node);
        if(node.getId() != null)
        {
            node.getId().apply(this);
        }
        if(node.getArgList() != null)
        {
            node.getArgList().apply(this);
        }
        outAFunctionCall(node);
    }

    public void inAArgList(AArgList node)
    {
        defaultIn(node);
    }

    public void outAArgList(AArgList node)
    {
        defaultOut(node);
    }

    public void caseAArgList(AArgList node)
    {
        inAArgList(node);
        if(node.getExpression() != null)
        {
            node.getExpression().apply(this);
        }
        {
            Object temp[] = node.getMoreExp().toArray();
            for(int i = 0; i < temp.length; i++)
            {
                ((PMoreExp) temp[i]).apply(this);
            }
        }
        outAArgList(node);
    }

    public void inAMoreExp(AMoreExp node)
    {
        defaultIn(node);
    }

    public void outAMoreExp(AMoreExp node)
    {
        defaultOut(node);
    }

    public void caseAMoreExp(AMoreExp node)
    {
        inAMoreExp(node);
        if(node.getExpression() != null)
        {
            node.getExpression().apply(this);
        }
        outAMoreExp(node);
    }

    public void inANumberValue(ANumberValue node)
    {
        defaultIn(node);
    }

    public void outANumberValue(ANumberValue node)
    {
        defaultOut(node);
    }

    public void caseANumberValue(ANumberValue node)
    {
        inANumberValue(node);
        if(node.getNumber() != null)
        {
            node.getNumber().apply(this);
        }
        outANumberValue(node);
    }

    public void inAStringValue(AStringValue node)
    {
        defaultIn(node);
    }

    public void outAStringValue(AStringValue node)
    {
        defaultOut(node);
    }

    public void caseAStringValue(AStringValue node)
    {
        inAStringValue(node);
        if(node.getString() != null)
        {
            node.getString().apply(this);
        }
        outAStringValue(node);
    }

    public void inAIntNumber(AIntNumber node)
    {
        defaultIn(node);
    }

    public void outAIntNumber(AIntNumber node)
    {
        defaultOut(node);
    }

    public void caseAIntNumber(AIntNumber node)
    {
        inAIntNumber(node);
        if(node.getInteger() != null)
        {
            node.getInteger().apply(this);
        }
        outAIntNumber(node);
    }
}