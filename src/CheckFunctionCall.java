/*
 * 	-------���� ������-------
 * 
 * �������� ���������� - 3120036
 * ������� ��������� - 3120124
 * ������� ������� - 3120133
 * ������ �������� - 3120209
 * 
 */

/*				������� ������ ����������
 * 
 *  � ����� ���� ���������� �� ��� ������ ������� ��������� ��� ������� ��
 *  ��������� ���� ��� ����� ���� ����������.
 *  
 *  ������������ ����� Override �� ������ inAFunctionCall � ����� �������������� �����
 *  ���������� ���� ������ ������ ������� ��� ����� ��� ����� ���� ����������.
 *  
 *   �������:
 *   	1. ��� ����� ���������� ��� ��� ���� �������
 *   	2. ��� ����� ���������� �� ����� ����������� ��� ����� ��� ����� �������
 * 
 */

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;

import minipython.analysis.DepthFirstAdapter;
import minipython.node.*;

public class CheckFunctionCall extends DepthFirstAdapter {
	private Hashtable localVars;
	private Hashtable symtable;

	public CheckFunctionCall(Hashtable symtable, Hashtable localVars) {
		this.localVars = localVars;
		this.symtable = symtable;
	}

	public void inAFunctionCall(AFunctionCall node) {
		String callId = node.getId().getText();
		int line = node.getId().getLine();
		int pos = node.getId().getPos();

		//	������� �� ���� ������� � ��������� ��� ����� �� ������������ �����
		if (!this.symtable.containsKey(callId)) {
			System.out.println(
					"Called function [" + callId + "] at line " + line + " at pos " + pos + " is not defined!");
			//	������ ������ �� ������ 3
			System.exit(-3);
		} else {
			//	����� ��� �������� ��� ���������� ��� ��������� ����������
			ArrayList STArgs = ((ArrayList) (((ArrayList) this.symtable.get(callId)).get(0)));
			
			//	����� ��� �������� ��� ���������� ��� ��������� ����������
			ArrayList callArgs = null;
			
			//	�������� ���������� ��������� ����������
			int numSTArgs = STArgs.size();
			//	������� ���������� ��� ����� default ����
			int defArgs = 0;

			//	����������� ������� ��������������� ����������
			for (int index = 0; index < numSTArgs; index++) {
				AbstractMap.SimpleEntry arg = (AbstractMap.SimpleEntry) STArgs.get(index);

				if (arg.getValue() != null) {
					defArgs++;
				}
			}

			//	������� ���������� ��������� ����������
			int calledNumArgs = -1;
			
			//	������ ��� ����� �� ����� ���������� ��� ��������� ����������
			PArgList arglist = node.getArgList();
			
			//	�������� ������
			arglist.apply(this);
			

			if (this.symtable.containsKey(arglist)) {
				callArgs = (ArrayList) this.symtable.get(arglist);
				//	������� ����� ��� �� ���������� ��� ���������
				calledNumArgs = callArgs.size();
				this.symtable.remove(arglist);
			}

			//	������� ��� ����� ����� ���������� ��� ����� ��� ����������� ���
			/*	�� � ������� ���������� ��� ��������� ���������� > ������� ���������� ��� ��������� ����������
			 * 	� �� � ������� ���������� ��� ��������� < ������� ���������� ��� ��������� - ������� default ����������
			 * 	���� �������� ������ ��� ��������� �� ���������.
			 */
			if (calledNumArgs > numSTArgs || (calledNumArgs < numSTArgs - defArgs)) {
				System.out.println("Wrong call of function [" + callId + "] at line " + line + " at pos " + pos
						+ ".\nCheck your arguments!");
				System.exit(-5);
			} else {
				PStatement stat = ((PStatement) (((ArrayList) this.symtable.get(callId)).get(1)));
				
				//stat.apply(new CompleteSymbolsTable(symtable, localVars));
				
				if (this.localVars.containsKey(stat)) {
					Object val = ((ArrayList) this.localVars.get(stat)).get(0);
				}
			}
		}
	}

	//	Visitor ��� ��� ����� inAArgList - ���������� ��� ������ ���������� ��� ��������� ����������	
	public void inAArgList(AArgList node) {
		PExpression exp = node.getExpression();
		LinkedList moreExp = node.getMoreExp();

		ArrayList calledParams = new ArrayList<>();

		exp.apply(new CompleteSymbolsTable(symtable, localVars));

		if (this.localVars.containsKey(exp)) {
			Object val = ((ArrayList) this.localVars.get(exp)).get(0);
			calledParams.add(new AbstractMap.SimpleEntry(exp, val));
		}

		for (int index = 0; index < moreExp.size(); index++) {
			PMoreExp moreE = (PMoreExp) moreExp.get(index);
			moreE.apply(this);

			if (this.localVars.containsKey(moreE)) {
				Object val = ((ArrayList) this.localVars.get(moreE)).get(0);
				calledParams.add(new AbstractMap.SimpleEntry(moreE, val));
			}
		}

		this.symtable.put(node, calledParams);
	}

	//	Visitor ��� ��� ����� inAMoreExp
	public void inAMoreExp(AMoreExp node) {
		PExpression exp = node.getExpression();
		exp.apply(new CompleteSymbolsTable(symtable, localVars));
		
		if (this.localVars.containsKey(exp)) {
			this.localVars.put(node, this.localVars.get(exp));
		}
	}
}
