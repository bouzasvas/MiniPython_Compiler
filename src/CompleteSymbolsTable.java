/*
 * 	-------���� ������-------
 * 
 * �������� ���������� - 3120036
 * ������� ��������� - 3120124
 * ������� ������� - 3120133
 * ������ �������� - 3120209
 * 
 */

/*
 * 				����� ��� ������� ��� ������ ��������
 * 
 * 	� ����� ���� ���������� �� ��� ������ ������� ��������� ��� ������� ��
 * 	��������� ���� �� ������������ ��� ������������ MiniPython.
 * 
 * 	������������ ����� ������ ����� ���� ���������� ��������:
 * 		1. ����� �� ��������� ����������
 * 		2. ����� String ���������� �� ������� ���
 * 	������� ������ �������� ��� ������� ������� ��� ���������� 
 * 		3. ��������� ������� ���������� �� ��� ���� ������ ���������
 * 
 */

import minipython.analysis.*;
import minipython.node.*;
import java.util.*;

public class CompleteSymbolsTable extends DepthFirstAdapter {
	private Hashtable localVars;
	private Hashtable symtable;

	CompleteSymbolsTable(Hashtable symtable, Hashtable localVars) {
		this.localVars = localVars;
		this.symtable = symtable;
	}

	// ********************Function****************************
	// ������ ���������� ��� �������� ��� ���� ������ ��������
	public void inAFuncFunction(AFuncFunction node) {
		// ����� ����������
		String id = node.getId().getText();
		int line = node.getId().getLine();
		int pos = node.getId().getPos();

		PArgument args = node.getArgument();
		ArrayList argsList = null;
		PStatement stat = node.getStatement();

		// �� ��������� ��� ��� ������� ��� Symbols Table ������ �� ������� ���
		// ��� ��� ��������
		if (!this.symtable.containsKey(id)) {
			// ���������� ���������� ����������
			if (args != null) {
				args.apply(this);

				if (this.localVars.get(args) != null) {
					/*
					 * � ����� argsStat ��������: 1. ��� 1� �������� ��� �����
					 * �� ���� ��� ����������� ��� ���������� ��� ��� default
					 * ����� ���� 2. ��� 2� �������� ��� ������� ��� ���������
					 */
					ArrayList argsStat = new ArrayList<>();
					argsList = (ArrayList) this.localVars.get(args);

					argsStat.add(argsList);
					argsStat.add(stat);

					// ������ ���� ������ �������� ��������� �� Key �� ����� ���
					// ����������
					// ��� �� Value � ����� ��� �������� ��� ����������� ��� ���
					// ������� ��� ����������
					this.symtable.put(id, argsStat);
				}
			}
			stat.apply(this);
		} else { // �� ��������� ��� ������� �������� ��������� �� �� ���� �����
			ArrayList definedFunction = (ArrayList) this.symtable.get(id);
			// ����� ��� �������� ��� ���������� ��� ��������� ����������
			ArrayList STArgs = ((ArrayList) (definedFunction.get(0)));

			// �������� ��� Symbols Table ��� ���� ����������
			id += "_defined";
			// ���������� ���������� ���� ����������
			if (args != null) {
				args.apply(this);

				if (this.localVars.get(args) != null) {
					/*
					 * � ����� argsStat ��������: 1. ��� 1� �������� ��� �����
					 * �� ���� ��� ����������� ��� ���������� ��� ��� default
					 * ����� ���� 2. ��� 2� �������� ��� ������� ��� ���������
					 */
					ArrayList argsStat = new ArrayList<>();
					argsList = (ArrayList) this.localVars.get(args);

					argsStat.add(argsList);
					argsStat.add(stat);

					// ������ ���� ������ �������� ��������� �� Key �� ����� ���
					// ����������
					// ��� �� Value � ����� ��� �������� ��� ����������� ��� ���
					// ������� ��� ����������
					this.symtable.put(id, argsStat);
				}
			}

			// ����� ��� �������� ��� ���������� ��� ���� ����������
			ArrayList newFunction = (ArrayList) this.symtable.get(id);
			ArrayList newArgs = ((ArrayList) (definedFunction.get(0)));

			// �������� ���������� ��������� ����������
			int numSTArgs = STArgs.size();
			// ������� ���������� ��� ����� default ����
			int defArgs = 0;

			// ����������� ������� ��������������� ����������
			for (int index = 0; index < numSTArgs; index++) {
				AbstractMap.SimpleEntry arg = (AbstractMap.SimpleEntry) STArgs.get(index);

				if (arg.getValue() != null) {
					defArgs++;
				}
			}

			// ������� ���������� ���� ����������
			int definedNumArgs = newArgs.size();
			int newDefArgs = 0;

			// ����������� ������� ��������������� ���������� ���� ����������
			for (int index = 0; index < definedNumArgs; index++) {
				AbstractMap.SimpleEntry arg = (AbstractMap.SimpleEntry) newArgs.get(index);

				if (arg.getValue() != null) {
					newDefArgs++;
				}
			}

			//	������� �� ��������������� � ������ ���� ���������� ����������
			if (numSTArgs == definedNumArgs || numSTArgs == definedNumArgs - newDefArgs || numSTArgs - defArgs == definedNumArgs) {
				//	�������� ��� ����� ��������� ���������� ��� �� Symbols Table
				this.symtable.remove(id);
				id = id.replace("_defined", "");
				System.out.println("Function [" + id + "] at line " + line + " at pos " + pos + " is already defined!");
				System.exit(-5);
			}
		}
	}

	// �������� ��� ��������� ������������� ���������� ��� ���������� ��� ��
	// symtable ���� ��� ����� ��� ��� ����� AFuncFunction
	public void outAFuncFunction(AFuncFunction node) {
		String fName = node.getId().getText();
		PStatement stat = node.getStatement();

		ArrayList argsList = (ArrayList) ((ArrayList) this.symtable.get(fName)).get(0);

		for (Object ob : argsList) {
			Object obKey = ((AbstractMap.SimpleEntry) ob).getKey();
			this.symtable.remove(obKey);
		}
	}

	// ���������� ��� �������� ��� ��������� ���� ���������� ���� ������
	// ��������
	public void inAArgArgument(AArgArgument node) {
		// ����� ����������
		String arg1 = node.getId().getText();
		int line = node.getId().getLine();
		Object arg1Val = null;

		// ������� ��� ������ Default �����
		PAssignValue defaultArg1Val = node.getAssignValue();
		// ������� �� ���������� ��� ����� ����������
		LinkedList moreArgs = node.getMoreArgs();

		// ����� ��� ���������� ���������� �� ��� default ����� ����
		ArrayList arguments = new ArrayList<>();

		if (defaultArg1Val != null) {
			defaultArg1Val.apply(this);

			if (this.localVars.get(defaultArg1Val) != null) {
				arg1Val = this.localVars.get(defaultArg1Val);
				arguments.add(new AbstractMap.SimpleEntry(arg1, arg1Val));
			}
		} else {
			arguments.add(new AbstractMap.SimpleEntry(arg1, null));
		}

		// �������� ��� ���������� ���� ������ �������� ��� �� scope
		// ��� ����������. ��� �������� �� ���������.
		this.symtable.put(arg1, 0);

		// �������� ������ �� ����������� ��� ���������� ��� 1� ���
		// �������� ���� ��� ����� ���� �� ��� default ����� ����
		for (int index = 0; index < moreArgs.size(); index++) {
			PMoreArgs moreA = (PMoreArgs) moreArgs.get(index);

			if (moreA != null)
				moreA.apply(this);

			if (this.localVars.get(moreA) != null) {
				ArrayList argParams = (ArrayList) this.localVars.get(moreA);
				String arg = (String) argParams.get(0);
				Object val = argParams.get(1);

				if (((AbstractMap.SimpleEntry) arguments.get(index)).getValue() != null && val == null) {
					System.out.println("Wrong function definition at line " + line
							+ "\nArguments with default values should always be at the end of argument list");
					System.exit(-5);
				}

				arguments.add(new AbstractMap.SimpleEntry(arg, val));

				// �������� ��� ���������� ���� ������ �������� ��� �� scope
				// ��� ����������. ��� �������� �� ���������.
				this.symtable.put(arg, 0);
			}
		}

		this.localVars.put(node, arguments);
	}

	// Visitor ��� ���������� �� ��� Default ����� ��� ���������� ����
	// ����������
	public void inAAssignValue(AAssignValue node) {
		PValue val = node.getValue();
		val.apply(this);

		if (this.localVars.get(val) != null) {
			Object value = ((ArrayList) this.localVars.get(val)).get(0);

			this.localVars.put(node, value);
		}
	}

	// Visitor ��� ��� ����������� (����� ��� 1��) ���� ���������� ��� ���
	// default ����� ����
	public void inAMoreArgs(AMoreArgs node) {
		String arg = node.getId().getText();

		PAssignValue val = node.getAssignValue();

		if (val != null) {
			val.apply(this);

			if (this.localVars.get(val) != null) {
				ArrayList argParams = new ArrayList<>();
				argParams.add(arg);
				argParams.add(this.localVars.get(val));
				this.localVars.put(node, argParams);
			}
		} else {
			ArrayList argParams = new ArrayList<>();
			argParams.add(arg);
			argParams.add(null);
			this.localVars.put(node, argParams);
		}
	}
	// ********************************************

	// ****************Statements******************
	/*
	 * ��� �������� �������� ������ ��������� ���� ������� ��� �������
	 * Statements
	 * 
	 * ������������: 1. ��� ���� ������� if, while ��������� �� ������ �� �����
	 * � �������� ������ ��� ����� ��� ��� �� ���� ���� ����������� (���� ���
	 * apply()) ���� ������� comparison ��� ���� ������� statement.
	 * 
	 * 2. ��� ��� ����� for ��������� �� ���� ������� � ��������� ���
	 * ����������� ����� in.
	 * 
	 * 3. ��� ���� ������� return, print, op, list ����������� ������� �����
	 * expression ��� �� ���������� ��������.
	 */
	public void inAIfStatement(AIfStatement node) {
		PComparison comp = node.getComparison();
		PStatement stat = node.getStatement();

		comp.apply(this);
		stat.apply(this);
	}

	public void inAWhileStatement(AWhileStatement node) {
		PComparison comp = node.getComparison();
		PStatement stat = node.getStatement();

		comp.apply(this);
		stat.apply(this);
	}

	public void inAForStatement(AForStatement node) {
		String id = node.getId2().getText();
		int line = node.getId2().getLine();
		int pos = node.getId2().getPos();

		PStatement stat = node.getStatement();
		stat.apply(this);

		if (!this.symtable.containsKey(id)) {
			System.out.println("Id [" + id + "] at line " + line + " at pos " + pos + " is not defined!");
			System.exit(-1);
		}
	}

	public void inAReturnStatement(AReturnStatement node) {
		PExpression exp = node.getExpression();
		exp.apply(this);
	}

	public void inAPrintStatement(APrintStatement node) {
		PExpression exp = node.getExpression();
		exp.apply(this);
	}

	public void inAOpStatement(AOpStatement node) {
		String id = node.getId().getText();

		PExpression valueExp = ((node.getExpression()));
		valueExp.apply(this);

		if (this.localVars.containsKey(valueExp)) {
			Object value = ((ArrayList) this.localVars.get(valueExp)).get(0);
			this.symtable.put(id, value);

			this.localVars.clear();
			// System.out.println(this.symtable);
		}
	}

	public void inAListStatement(AListStatement node) {
		// ����� ������
		String id = node.getId().getText();
		int line = node.getId().getLine();
		int pos = node.getId().getPos();

		// � ����� ��� �� ��������� ��� �����
		ArrayList list = null;

		// �������� ������� ��� ������� ��������� ��� �� ������������
		PExpression insideExp = node.getExp1();
		// ����� ������� ��� ��� ���� ��� �� �������� ��� �������� ��������
		PExpression rightExp = node.getExp2();

		insideExp.apply(this);
		rightExp.apply(this);

		int listSize = 0;

		// ������� �� ���� ������� � ����� ��� ���� �� ��������������
		if (!this.symtable.containsKey(id)) {
			System.out.println("List [" + id + "] at line " + line + " at pos " + pos + " is not defined");
			System.exit(-4);
		} else {
			list = (ArrayList) (this.symtable.get(id));
			listSize = list.size();
		}

		if (this.localVars.get(insideExp) != null) {
			Object exp = ((ArrayList) this.localVars.get(insideExp)).get(0);

			if (exp instanceof String) {
				System.out.println("Dictionary is not supported for this version of miniPython!");
				System.exit(-4);
			} else {
				// ������� ��� �������� ������
				// �� ��������� ��� ������� �� ������� ��� ������ �����������
				// ���������
				// ������ ��� ������������ �� ���������
				int index = (int) exp;
				if (index > listSize || index < 0) {
					System.out.println("Index out of bounds: " + index + " out of list size " + listSize);
					System.exit(-4);
				} else {
					// ����������� ��������� ��� ������
					ArrayList listParams = new ArrayList<>();
					Object rightValue = ((ArrayList) this.localVars.get(rightExp)).get(0);
					list.add(index, rightValue);

					listParams.add(list);
					listParams.add(line);

					this.symtable.put(id, listParams);
				}
			}
		}
	}
	// ************************************************

	// ***************Expressions**********************
	/*
	 * ��� �������� �������� ������ ����������� ������� ����� Expression.
	 *
	 * ������������: 1. ��������������� �������� ��� ������� ���������,
	 * ���������, ���/����, ���������, ������, ������������� ��� ��������������
	 * ��������. ���������� ��������� �� ����� ������� �� ���������� ���
	 * ���������������� ����� ������ ��� �� ����������� � �������� �����. ��. ��
	 * ������ �� ����� �������� ������ ���� integer ��� ���� String.
	 *
	 * 2. ��������� �� ���� ������� ��� ��������� ������������ ��� �����
	 * AIdExpression.
	 *
	 * 3. ��������� ��� ����� ��� ���� ������� AValueExpression.
	 */
	public void inAAddExpression(AAddExpression node) {
		// �������� �������
		PExpression leftExp = node.getLeft();
		// ����� ��������� ��������
		Object typeOfL = null;
		// ���� ��������� ��������
		Object leftVal = null;
		int leftLine = -1;

		// ���������� �� ��������...
		PExpression rightExp = node.getRight();
		Object typeOfR = null;
		Object rightVal = null;
		int rightLine = -1;

		leftExp.apply(this);
		rightExp.apply(this);

		if (this.localVars.get(leftExp) != null) {
			ArrayList expParams = (ArrayList) this.localVars.remove(leftExp);

			leftVal = expParams.get(0);
			leftLine = (int) expParams.get(1);

			// ������� ����� ����������
			if (leftVal.getClass().equals(new Integer(0).getClass())) {
				typeOfL = new Integer(0).getClass();
			} else
				typeOfL = "".getClass();
		}
		if (this.localVars.get(rightExp) != null) {
			ArrayList expParams = (ArrayList) this.localVars.remove(rightExp);

			rightVal = expParams.get(0);
			rightLine = (int) expParams.get(1);

			// ������� ����� ����������
			if (rightVal.getClass().equals(new Integer(0).getClass())) {
				typeOfR = new Integer(0).getClass();
			} else
				typeOfR = "".getClass();
		}

		// ������� �� �� 2 ��������� ����� ��� ����� ����� ��� ��������
		// ���������� ��������� ���������
		if (!typeOfL.equals(typeOfR)) {
			System.out.println("Addition between [" + leftVal + "]:" + typeOfL + " at line " + leftLine + " and ["
					+ rightVal + "]:" + typeOfR + " at line " + rightLine + " is not allowed!");
			System.exit(-2);
		} else {
			// �������� ����� ��� ������ HashMap ��� ����� ��� ��� �� symtable
			// ��� ��������
			ArrayList result = new ArrayList<>();
			Object val;
			if (typeOfL.equals("".getClass())) {
				val = (String) leftVal + (String) rightVal;
			} else {
				val = (Integer) leftVal + (Integer) rightVal;
			}
			result.add(val);
			result.add(leftLine);

			if (node.parent() instanceof AParenthesisExpression) {
				this.localVars.put(node.parent(), result);
			} else {
				this.localVars.put(node, result);
			}
		}
	}

	public void inASubExpression(ASubExpression node) {
		PExpression leftExp = node.getLeft();
		Object typeOfL = null;
		Object leftVal = null;
		int leftLine = -1;

		PExpression rightExp = node.getRight();
		Object typeOfR = null;
		Object rightVal = null;
		int rightLine = -1;

		leftExp.apply(this);
		rightExp.apply(this);

		if (this.localVars.get(leftExp) != null) {
			ArrayList expParams = (ArrayList) this.localVars.remove(leftExp);

			leftVal = expParams.get(0);
			leftLine = (int) expParams.get(1);

			if (leftVal.getClass().equals(new Integer(0).getClass())) {
				typeOfL = new Integer(0).getClass();
			} else
				typeOfL = "".getClass();
		}
		if (this.localVars.get(rightExp) != null) {
			ArrayList expParams = (ArrayList) this.localVars.remove(rightExp);

			rightVal = expParams.get(0);
			rightLine = (int) expParams.get(1);

			if (rightVal.getClass().equals(new Integer(0).getClass())) {
				typeOfR = new Integer(0).getClass();
			} else
				typeOfR = "".getClass();
		}

		if (!typeOfL.equals(typeOfR)) {
			System.out.println("Subtraction between [" + leftVal + "]:" + typeOfL + " at line " + leftLine + " and ["
					+ rightVal + "]:" + typeOfR + " at line " + rightLine + " is not allowed!");
			System.exit(-2);
		} else {
			ArrayList result = new ArrayList<>();
			Object val = null;
			if (typeOfL.equals("".getClass())) {
				System.out.println("Subtraction between [" + leftVal + "], [" + rightVal + "]" + ":" + typeOfL
						+ " is not allowed!");
				System.exit(-3);
			} else {
				val = (Integer) leftVal - (Integer) rightVal;
			}
			result.add(val);
			result.add(leftLine);

			if (node.parent() instanceof AParenthesisExpression) {
				this.localVars.put(node.parent(), result);
			} else {
				this.localVars.put(node, result);
			}
		}
	}

	public void inAMultiplicationExpression(AMultiplicationExpression node) {
		PExpression leftExp = node.getLeft();
		Object typeOfL = null;
		Object leftVal = null;
		int leftLine = -1;

		PExpression rightExp = node.getRight();
		Object typeOfR = null;
		Object rightVal = null;
		int rightLine = -1;

		leftExp.apply(this);
		rightExp.apply(this);

		if (this.localVars.get(leftExp) != null) {
			ArrayList expParams = (ArrayList) this.localVars.remove(leftExp);

			leftVal = expParams.get(0);
			leftLine = (int) expParams.get(1);

			if (leftVal.getClass().equals(new Integer(0).getClass())) {
				typeOfL = new Integer(0).getClass();
			} else
				typeOfL = "".getClass();
		}
		if (this.localVars.get(rightExp) != null) {
			ArrayList expParams = (ArrayList) this.localVars.remove(rightExp);

			rightVal = expParams.get(0);
			rightLine = (int) expParams.get(1);

			if (rightVal.getClass().equals(new Integer(0).getClass())) {
				typeOfR = new Integer(0).getClass();
			} else
				typeOfR = "".getClass();
		}

		if (!typeOfL.equals(typeOfR)) {
			System.out.println("Multiplication between [" + leftVal + "]:" + typeOfL + " at line " + leftLine + " and ["
					+ rightVal + "]:" + typeOfR + " at line " + rightLine + " is not allowed!");
			System.exit(-2);
		} else {
			ArrayList result = new ArrayList<>();
			Object val = null;
			if (typeOfL.equals("".getClass())) {
				System.out.println("Multiplication between [" + leftVal + "], [" + rightVal + "]" + ":" + typeOfL
						+ " is not allowed!");
				System.exit(-3);
			} else {
				val = (Integer) leftVal * (Integer) rightVal;
			}
			result.add(val);
			result.add(leftLine);

			if (node.parent() instanceof AParenthesisExpression) {
				this.localVars.put(node.parent(), result);
			} else {
				this.localVars.put(node, result);
			}
		}
	}

	public void inADivisionExpression(ADivisionExpression node) {
		PExpression leftExp = node.getLeft();
		Object typeOfL = null;
		Object leftVal = null;
		int leftLine = -1;

		PExpression rightExp = node.getRight();
		Object typeOfR = null;
		Object rightVal = null;
		int rightLine = -1;

		leftExp.apply(this);
		rightExp.apply(this);

		if (this.localVars.get(leftExp) != null) {
			ArrayList expParams = (ArrayList) this.localVars.remove(leftExp);

			leftVal = expParams.get(0);
			leftLine = (int) expParams.get(1);

			if (leftVal.getClass().equals(new Integer(0).getClass())) {
				typeOfL = new Integer(0).getClass();
			} else
				typeOfL = "".getClass();
		}
		if (this.localVars.get(rightExp) != null) {
			ArrayList expParams = (ArrayList) this.localVars.remove(rightExp);

			rightVal = expParams.get(0);
			rightLine = (int) expParams.get(1);
			if (rightVal.equals(0)) {
				System.out.println("Division by zero" + " at line " + rightLine + ". Exiting...");
				System.exit(-2);
			}
			if (rightVal.getClass().equals(new Integer(0).getClass())) {
				typeOfR = new Integer(0).getClass();
			} else
				typeOfR = "".getClass();
		}

		if (!typeOfL.equals(typeOfR)) {
			System.out.println("Division between [" + leftVal + "]:" + typeOfL + " at line " + leftLine + " and ["
					+ rightVal + "]:" + typeOfR + " at line " + rightLine + " is not allowed!");
			System.exit(-2);
		} else {
			ArrayList result = new ArrayList<>();
			Object val = null;
			if (typeOfL.equals("".getClass())) {
				System.out.println(
						"Division between [" + leftVal + "], [" + rightVal + "]" + ":" + typeOfL + " is not allowed!");
				System.exit(-3);
			} else {
				val = (Integer) leftVal / (Integer) rightVal;
			}
			result.add(val);
			result.add(leftLine);

			if (node.parent() instanceof AParenthesisExpression) {
				this.localVars.put(node.parent(), result);
			} else {
				this.localVars.put(node, result);
			}
		}
	}

	// ������� ��� ��������������� ��� ������� ������ �� ���������
	public void inAListExpression(AListExpression node) {
		// ����� ������
		String id = node.getId().getText();
		int line = node.getId().getLine();
		int pos = node.getId().getPos();

		// ������� ��� ��� ����� �� �������� �� ������� ��� ������
		PExpression listExp = node.getExpression();

		listExp.apply(this);

		if (this.localVars.get(listExp) != null) {
			Object exp = ((ArrayList) this.localVars.get(listExp)).get(0);

			if (exp instanceof String) {
				System.out.println("Dictionary is not supported for this version of miniPython!");
				System.exit(-4);
			} else {

				ArrayList listParams = new ArrayList<>();
				ArrayList list = new ArrayList<>((int) exp);

				listParams.add(list);
				listParams.add(line);

				// �������� ������ ��� ������ HashTable �� ����� ��
				// ��������������
				// �������� ��� ��� ������ ��������
				this.localVars.put(node, listParams);
			}
		}
	}

	public void inAPrePlusPlusExpression(APrePlusPlusExpression node) {
		node.getPrePostElements().apply(this);
	}

	public void inAPreMinusMinusExpression(APreMinusMinusExpression node) {
		node.getPrePostElements().apply(this);
	}

	public void inAPostPlusPlusExpression(APostPlusPlusExpression node) {
		node.getPrePostElements().apply(this);
	}

	public void inAPostMinusMinusExpression(APostMinusMinusExpression node) {
		node.getPrePostElements().apply(this);
	}

	public void inAValueExpression(AValueExpression node) {
		node.getValue().apply(this);
	}

	// ������� ��� ������� �� ��� ��������� ���� ������� ������������ ��� �����
	// AIdExpression
	public void inAIdExpression(AIdExpression node) {
		String id = node.getId().getText();
		int line = node.getId().getLine();
		int pos = node.getId().getPos();

		if (!this.symtable.containsKey(id)) {
			System.out.println("Id [" + id + "] at line " + line + " at pos " + pos + " is not defined!");
			System.exit(-1);
		} else {
			ArrayList idParams = new ArrayList<>();

			Object val = this.symtable.get(id);

			idParams.add(val);
			idParams.add(line);
			idParams.add(pos);

			this.localVars.put(node, idParams);
		}
	}

	// ������� ��� ��������������� ��� ��� ������� �� ������������� ���
	// �������������� �������� �� �����
	public void inAListPrePostElements(AListPrePostElements node) {
		PExpression exp = node.getExpression();
		ArrayList list = (ArrayList) this.symtable.get(node.getId().getText());
		int line = node.getId().getLine();

		exp.apply(this);

		if (this.localVars.containsKey(exp)) {
			Object val = ((ArrayList) (this.localVars.get(exp))).get(0);

			if (val instanceof String) {
				System.out.println("Dictionary is not supported for this version of miniPython!");
				System.exit(-4);
			} else {
				// ������� ��� ������ ��� �������� ��������� �� ��������� ���
				// ������� �� ������� ��� ������
				int index = (int) val;
				if (index > list.size() || index < 0) {
					System.out.println("Index out of bounds: " + index + " out of list size " + list.size());
					System.exit(-4);
				} else {
					ArrayList prepostParams = new ArrayList<>();
					// ���� ��� ������ ��� �������� index
					int listIndexValue = (int) ((ArrayList) list.get(index)).get(0);

					// ������� ��� �� ����� ����� � �������� ������ ��� ��������
					// ���
					// ����������� ������
					if (node.parent() instanceof APrePlusPlusExpression) {
						prepostParams.add(++listIndexValue);
					} else if (node.parent() instanceof APostPlusPlusExpression
							|| node.parent() instanceof APostMinusMinusExpression) {
						prepostParams.add(listIndexValue);
					} else {
						prepostParams.add(--listIndexValue);
					}
					prepostParams.add(line);
					this.localVars.put(node.parent(), prepostParams);
				}
			}
		}
	}

	// ������� ��� ��������������� ��� ��� ������� �� �������������
	// ��� �������������� �������� �� ���������
	public void inAIdPrePostElements(AIdPrePostElements node) {
		String id = node.getId().getText();
		int line = node.getId().getLine();
		int pos = node.getId().getPos();

		if (!this.symtable.containsKey(id)) {
			System.out.println("Id " + id + " at line " + line + " at pos " + pos + " is not defined!");
			System.exit(-1);
		} else {
			Object val = this.symtable.get(id);
			if (val instanceof String) {
				System.out.println("Prefix-Postfix operations cannot be performed on String Id [" + id + "]");
				System.exit(-3);
			} else {
				int intValue = (int) val;
				if (node.parent() instanceof APrePlusPlusExpression) {
					this.symtable.put(id, ++intValue);
				} else if (node.parent() instanceof APostPlusPlusExpression
						|| node.parent() instanceof APostMinusMinusExpression) {
					this.symtable.put(id, intValue);
				} else {
					this.symtable.put(id, --intValue);
				}
			}
		}
	}
	// ************************************************************

	// ********************Comparisons*****************************
	/*
	 * ��� �������� �������� ������ ����������� ������� ����� Comparison.
	 * 
	 * ������������: ��� ����� ���� ������� ��������� ������ ���� great, less,
	 * eq, noteq ��������� ��� ��������� ��� ��� ������ ����������������
	 * �������� ��� ����������� �������� ��������� ���� ����������. �� �� ������
	 * �� ��������������� �������� ������� �� ������ Integer ��� String.
	 */
	public void inAGreatComparison(AGreatComparison node) {
		PExpression leftExp = node.getExp1();
		int leftLine = -1;
		Object leftValue = null;
		Object leftType = null;

		PExpression rightExp = node.getExp2();
		int rightLine = -1;
		Object rightValue = null;
		Object rightType = null;

		leftExp.apply(this);
		rightExp.apply(this);

		if (this.localVars.containsKey(leftExp)) {
			ArrayList leftParams = (ArrayList) this.localVars.get(leftExp);

			leftValue = leftParams.get(0);
			leftLine = (int) leftParams.get(1);
			leftType = leftValue.getClass();
		}

		if (this.localVars.containsKey(leftExp)) {
			ArrayList rightParams = (ArrayList) this.localVars.get(rightExp);

			rightValue = rightParams.get(0);
			rightLine = (int) rightParams.get(1);
			rightType = rightValue.getClass();
		}

		// ������� �� �� 2 ��������� ����� ��� ����� �����
		if (!leftType.equals(rightType)) {
			System.out.println("Comparison between [" + leftValue + "]:" + leftType + " at line " + leftLine + " and ["
					+ rightValue + "]:" + rightType + " at line " + rightLine + " is not allowed!");
			System.exit(-2);
		} else {
			// nothing
		}
	}

	public void inALessComparison(ALessComparison node) {
		PExpression leftExp = node.getExp1();
		int leftLine = -1;
		Object leftValue = null;
		Object leftType = null;

		PExpression rightExp = node.getExp2();
		int rightLine = -1;
		Object rightValue = null;
		Object rightType = null;

		leftExp.apply(this);
		rightExp.apply(this);

		if (this.localVars.containsKey(leftExp)) {
			ArrayList leftParams = (ArrayList) this.localVars.get(leftExp);

			leftValue = leftParams.get(0);
			leftLine = (int) leftParams.get(1);
			leftType = leftValue.getClass();
		}

		if (this.localVars.containsKey(leftExp)) {
			ArrayList rightParams = (ArrayList) this.localVars.get(rightExp);

			rightValue = rightParams.get(0);
			rightLine = (int) rightParams.get(1);
			rightType = rightValue.getClass();
		}

		if (!leftType.equals(rightType)) {
			System.out.println("Comparison between [" + leftValue + "]:" + leftType + " at line " + leftLine + " and ["
					+ rightValue + "]:" + rightType + " at line " + rightLine + " is not allowed!");
			System.exit(-2);
		} else {
			// nothing
		}
	}

	public void inAEqComparison(AEqComparison node) {
		PExpression leftExp = node.getExp1();
		int leftLine = -1;
		Object leftValue = null;
		Object leftType = null;

		PExpression rightExp = node.getExp2();
		int rightLine = -1;
		Object rightValue = null;
		Object rightType = null;

		leftExp.apply(this);
		rightExp.apply(this);

		if (this.localVars.containsKey(leftExp)) {
			ArrayList leftParams = (ArrayList) this.localVars.get(leftExp);

			leftValue = leftParams.get(0);
			leftLine = (int) leftParams.get(1);
			leftType = leftValue.getClass();
		}

		if (this.localVars.containsKey(leftExp)) {
			ArrayList rightParams = (ArrayList) this.localVars.get(rightExp);

			rightValue = rightParams.get(0);
			rightLine = (int) rightParams.get(1);
			rightType = rightValue.getClass();
		}

		if (!leftType.equals(rightType)) {
			System.out.println("Comparison between [" + leftValue + "]:" + leftType + " at line " + leftLine + " and ["
					+ rightValue + "]:" + rightType + " at line " + rightLine + " is not allowed!");
			System.exit(-2);
		} else {
			// nothing
		}
	}

	public void inANoteqComparison(ANoteqComparison node) {
		PExpression leftExp = node.getExp1();
		int leftLine = -1;
		Object leftValue = null;
		Object leftType = null;

		PExpression rightExp = node.getExp2();
		int rightLine = -1;
		Object rightValue = null;
		Object rightType = null;

		leftExp.apply(this);
		rightExp.apply(this);

		if (this.localVars.containsKey(leftExp)) {
			ArrayList leftParams = (ArrayList) this.localVars.get(leftExp);

			leftValue = leftParams.get(0);
			leftLine = (int) leftParams.get(1);
			leftType = leftValue.getClass();
		}

		if (this.localVars.containsKey(leftExp)) {
			ArrayList rightParams = (ArrayList) this.localVars.get(rightExp);

			rightValue = rightParams.get(0);
			rightLine = (int) rightParams.get(1);
			rightType = rightValue.getClass();
		}

		if (!leftType.equals(rightType)) {
			System.out.println("Comparison between [" + leftValue + "]:" + leftType + " at line " + leftLine + " and ["
					+ rightValue + "]:" + rightType + " at line " + rightLine + " is not allowed!");
			System.exit(-2);
		} else {
			// nothing
		}
	}
	// ************************************************

	// *******************Value************************
	/*
	 * 
	 * ��� �������� �������� ������ ����������� ������� ����� Number ��� String
	 * 
	 * ������������: ��������� ��� ����� ��� ������ ��� ��� �������� ���� ������
	 * �����
	 * 
	 */
	public void inANumberValue(ANumberValue node) {
		node.getNumber().apply(this);
	}

	public void inAIntNumber(AIntNumber node) {
		// ������� ���� ��� ������
		int value = Integer.valueOf(node.getInteger().getText());
		int line = node.getInteger().getLine();
		int pos = node.getInteger().getPos();

		// ����� ��� ������� ����, ������ ��� ���� ��� ������
		ArrayList numberParams = new ArrayList<>();
		numberParams.add(value);
		numberParams.add(line);
		numberParams.add(pos);

		if (node.parent().parent() instanceof AValueExpression) {
			this.localVars.put(node.parent().parent(), numberParams);
		} else {
			this.localVars.put(node.parent(), numberParams);
		}
	}

	public void inAStringValue(AStringValue node) {
		// ������������ ��� ������
		String value = node.getString().getText();
		value = value.replace("\"", "");
		int line = node.getString().getLine();
		int pos = node.getString().getPos();

		// ����� ��� ������� ����, ������ ��� ���� ��� ������
		ArrayList stringParams = new ArrayList<>();
		stringParams.add(value);
		stringParams.add(line);
		stringParams.add(pos);

		if (node.parent() instanceof AValueExpression) {
			this.localVars.put(node.parent(), stringParams);
		} else {
			this.localVars.put(node, stringParams);
		}
	}
}
// *****************************************************