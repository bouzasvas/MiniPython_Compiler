/*
 * 	-------Μέλη Ομάδας-------
 * 
 * Διακάκης Ελευθέριος - 3120036
 * Μπούζας Βασίλειος - 3120124
 * Ντούλος Ξενοφών - 3120133
 * Χρόνης Γεώργιος - 3120209
 * 
 */

/*
 * 				Κλάση που γεμίζει τον Πίνακα Συμβόλων
 * 
 * 	Η κλάση αυτή ασχολείται με τον έλεγχο πιθανών σφαλμάτων που μπορούν να
 * 	προκύψουν κατά τη μεταγλώττιση του προγράμματος MiniPython.
 * 
 * 	Συγκεκριμένα κάνει μεταξύ άλλων τους ακόλουθους ελέγχους:
 * 		1. Χρήση μη δηλωμένης μεταβλητής
 * 		2. Χρήση String μεταβλητής ως ακέραιο και
 * 	πολλούς άλλους ελέγχους που αφορούν πράξεις και συγκρίσεις 
 * 		3. Επανάληψη δήλωσης συνάρτησης με τον ίδιο αριθμό ορισμάτων
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
	// Δήλωση συνάρτησης και προσθήκη της στον Πίνακα Συμβόλων
	public void inAFuncFunction(AFuncFunction node) {
		// Όνομα Συνάρτησης
		String id = node.getId().getText();
		int line = node.getId().getLine();
		int pos = node.getId().getPos();

		PArgument args = node.getArgument();
		ArrayList argsList = null;
		PStatement stat = node.getStatement();

		// Σε περίπτωση που δεν υπάρχει στο Symbols Table ελέγχω τη σύνταξη της
		// και την προσθέτω
		if (!this.symtable.containsKey(id)) {
			// Διαχείριση Παραμέτρων Συνάρτησης
			if (args != null) {
				args.apply(this);

				if (this.localVars.get(args) != null) {
					/*
					 * Η λίστα argsStat περιέχει: 1. Στο 1ο στοιχείο μια λίστα
					 * με όλες τις παραμέτρους της συνάρτησης και τις default
					 * τιμές τους 2. Στο 2ο στοιχείο τις εντολές της συάρτησης
					 */
					ArrayList argsStat = new ArrayList<>();
					argsList = (ArrayList) this.localVars.get(args);

					argsStat.add(argsList);
					argsStat.add(stat);

					// Τελικά στον πίνακα συμβόλων εισάγεται ως Key το όνομα της
					// συνάρτησης
					// και ως Value η λίστα που περιέχει τις παραμέτρους και τις
					// εντολές τις συνάρτησης
					this.symtable.put(id, argsStat);
				}
			}
			stat.apply(this);
		} else { // Σε περίπτωση που υπάρχει δηλωμένη συνάρτηση με το ίδιο όνομα
			ArrayList definedFunction = (ArrayList) this.symtable.get(id);
			// Λίστα που περιέχει τις μεταβλητές της δηλωμένης συνάρτησης
			ArrayList STArgs = ((ArrayList) (definedFunction.get(0)));

			// Προσθήκη στο Symbols Table της νέας συνάρτησης
			id += "_defined";
			// Διαχείριση Παραμέτρων νέας Συνάρτησης
			if (args != null) {
				args.apply(this);

				if (this.localVars.get(args) != null) {
					/*
					 * Η λίστα argsStat περιέχει: 1. Στο 1ο στοιχείο μια λίστα
					 * με όλες τις παραμέτρους της συνάρτησης και τις default
					 * τιμές τους 2. Στο 2ο στοιχείο τις εντολές της συάρτησης
					 */
					ArrayList argsStat = new ArrayList<>();
					argsList = (ArrayList) this.localVars.get(args);

					argsStat.add(argsList);
					argsStat.add(stat);

					// Τελικά στον πίνακα συμβόλων εισάγεται ως Key το όνομα της
					// συνάρτησης
					// και ως Value η λίστα που περιέχει τις παραμέτρους και τις
					// εντολές τις συνάρτησης
					this.symtable.put(id, argsStat);
				}
			}

			// Λίστα που περιέχει τις μεταβλητές της νέας συνάρτησης
			ArrayList newFunction = (ArrayList) this.symtable.get(id);
			ArrayList newArgs = ((ArrayList) (definedFunction.get(0)));

			// Αριρθμός Παραμέτρων Δηλωμένης Συνάρτησης
			int numSTArgs = STArgs.size();
			// Αριθμός Παραμέτρων που έχουν default τιμή
			int defArgs = 0;

			// Υπολογισμός αριθμού προκαθορισμένων παραμέτρων
			for (int index = 0; index < numSTArgs; index++) {
				AbstractMap.SimpleEntry arg = (AbstractMap.SimpleEntry) STArgs.get(index);

				if (arg.getValue() != null) {
					defArgs++;
				}
			}

			// Αριθμός παραμέτρων νέας συνάρτησης
			int definedNumArgs = newArgs.size();
			int newDefArgs = 0;

			// Υπολογισμός αριθμού προκαθορισμένων παραμέτρων νέας συνάρτησης
			for (int index = 0; index < definedNumArgs; index++) {
				AbstractMap.SimpleEntry arg = (AbstractMap.SimpleEntry) newArgs.get(index);

				if (arg.getValue() != null) {
					newDefArgs++;
				}
			}

			//	Έλεγχος αν επαναλαμβάνεται η δήλωση μιας υπάρχουσας συνάρτησης
			if (numSTArgs == definedNumArgs || numSTArgs == definedNumArgs - newDefArgs || numSTArgs - defArgs == definedNumArgs) {
				//	Αφαίρεση της λάθος ορισμένης συνάρτησης από το Symbols Table
				this.symtable.remove(id);
				id = id.replace("_defined", "");
				System.out.println("Function [" + id + "] at line " + line + " at pos " + pos + " is already defined!");
				System.exit(-5);
			}
		}
	}

	// Αφαίρεση των προσωρινά αποθηκευμένων παραμέτρων της συνάρτησης από το
	// symtable κατά την έξοδο από τον κόμβο AFuncFunction
	public void outAFuncFunction(AFuncFunction node) {
		String fName = node.getId().getText();
		PStatement stat = node.getStatement();

		ArrayList argsList = (ArrayList) ((ArrayList) this.symtable.get(fName)).get(0);

		for (Object ob : argsList) {
			Object obKey = ((AbstractMap.SimpleEntry) ob).getKey();
			this.symtable.remove(obKey);
		}
	}

	// Εντοπισμός και προσθήκη των παρμέτρων μιας συνάρτησης στον πίνακα
	// συμβόλων
	public void inAArgArgument(AArgArgument node) {
		// Όνομα παραμέτρου
		String arg1 = node.getId().getText();
		int line = node.getId().getLine();
		Object arg1Val = null;

		// Έλεγχος για ύπαρξη Default τιμής
		PAssignValue defaultArg1Val = node.getAssignValue();
		// Έλεγχος αν ακολουθούν και άλλες παράμετροι
		LinkedList moreArgs = node.getMoreArgs();

		// Λίστα για αποθήκευση παραμέτρων με τις default τιμές τους
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

		// Προσθήκη της μεταβλητής στον πίνακα συμβόλων για το scope
		// της συνάρτησης. Στη συνέχεια θα αφαιρεθεί.
		this.symtable.put(arg1, 0);

		// Διάσχιση λίστας με παραμέτρους που ακολουθούν την 1η και
		// προσθήκη τους στη λίστα μαζί με τις default τιμές τους
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

				// Προσθήκη της μεταβλητής στον πίνακα συμβόλων για το scope
				// της συνάρτησης. Στη συνέχεια θα αφαιρεθεί.
				this.symtable.put(arg, 0);
			}
		}

		this.localVars.put(node, arguments);
	}

	// Visitor που ασχολείται με τις Default τιμές των παραμέτρων μιας
	// συνάρτησης
	public void inAAssignValue(AAssignValue node) {
		PValue val = node.getValue();
		val.apply(this);

		if (this.localVars.get(val) != null) {
			Object value = ((ArrayList) this.localVars.get(val)).get(0);

			this.localVars.put(node, value);
		}
	}

	// Visitor για τις παραμέτρους (εκτός της 1ης) μιας συνάρτησης και τις
	// default τιμές τους
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
	 * Στα παρακάτω κομμάτια κώδικα αναλύουμε τους κόμβους που αφορούν
	 * Statements
	 * 
	 * Συγκεκριμένα: 1. Για τους κόμβους if, while ελέγχουμε αν μπορεί να γίνει
	 * η σύγκριση μεταξύ των τιμών και για το λόγο αυτό διασχίζουμε (μέσω της
	 * apply()) τους κόμβους comparison και τους κόμβους statement.
	 * 
	 * 2. Για τον κόμβο for ελέγχουμε αν έχει δηλωθεί η μεταβλητή της
	 * δεσμευμένης λέξης in.
	 * 
	 * 3. Για τους κόμβους return, print, op, list διασχίζουμε κόμβους τύπου
	 * expression που θα εξέτασουμε παρακάτω.
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
		// Όνομα λίστας
		String id = node.getId().getText();
		int line = node.getId().getLine();
		int pos = node.getId().getPos();

		// Η λίστα που θα φιλοξενεί τις τιμές
		ArrayList list = null;

		// Αριστερή έκφραση για επιλογή στοιχείου που θα τροποποιηθεί
		PExpression insideExp = node.getExp1();
		// Δεξιά έκφραση για την τιμή που θα ανατεθεί στο παραπάνω στοιχείο
		PExpression rightExp = node.getExp2();

		insideExp.apply(this);
		rightExp.apply(this);

		int listSize = 0;

		// Έλεγχος αν έχει δηλωθεί η λίστα που πάμε να τροποποιήσουμε
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
				// Έλεγχος του στοχείου δείκτη
				// Σε περίπτωση που υπερβεί το μέγεθος της λίστας εμφανίζουμε
				// κατάλληλο
				// μήνυμα και τερματίζουμε το πρόγραμμα
				int index = (int) exp;
				if (index > listSize || index < 0) {
					System.out.println("Index out of bounds: " + index + " out of list size " + listSize);
					System.exit(-4);
				} else {
					// Τροποποίηση στοιχείου της λίστας
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
	 * Στα παρακάτω κομμάτια κώδικα διασχίζουμε κόμβους τύπου Expression.
	 *
	 * Συγκεκριμένα: 1. Πραγματοποιούμε ελέγχους για κόμβους πρόσθεσης,
	 * αφαίρεσης, πολ/σμου, διαίρεσης, λίστας, προθεματικούς και μεταθεματικούς
	 * τελέστες. Ειδικότερα ελέγχουμε αν έχουν δηλωθεί οι μεταβλητές που
	 * χρησιμοποιούνται καθώς επίσης και αν επιτρέπεται η εκάστοτε πράξη. Πχ. δε
	 * μπορεί να γίνει πρόσθεση μεταξύ ενός integer και ενός String.
	 *
	 * 2. Ελέγχουμε αν έχει δηλωθεί μια μεταβλητή διασχίζοντας τον κόμβο
	 * AIdExpression.
	 *
	 * 3. Παίρνουμε τις τιμές από τους κόμβους AValueExpression.
	 */
	public void inAAddExpression(AAddExpression node) {
		// Αριστερή έκφραση
		PExpression leftExp = node.getLeft();
		// Τύπος αριστερής έκφρασης
		Object typeOfL = null;
		// Τιμή αριστερής έκφρασης
		Object leftVal = null;
		int leftLine = -1;

		// Αντίστοιχα με παραπάνω...
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

			// Ανάθεση τύπου μεταβλητής
			if (leftVal.getClass().equals(new Integer(0).getClass())) {
				typeOfL = new Integer(0).getClass();
			} else
				typeOfL = "".getClass();
		}
		if (this.localVars.get(rightExp) != null) {
			ArrayList expParams = (ArrayList) this.localVars.remove(rightExp);

			rightVal = expParams.get(0);
			rightLine = (int) expParams.get(1);

			// Ανάθεση τύπου μεταβλητής
			if (rightVal.getClass().equals(new Integer(0).getClass())) {
				typeOfR = new Integer(0).getClass();
			} else
				typeOfR = "".getClass();
		}

		// Έλεγχος αν οι 2 εκφράσεις είναι του ίδιου τύπου και εμφάνιση
		// κατάλληλου μηνύματος σφάλματος
		if (!typeOfL.equals(typeOfR)) {
			System.out.println("Addition between [" + leftVal + "]:" + typeOfL + " at line " + leftLine + " and ["
					+ rightVal + "]:" + typeOfR + " at line " + rightLine + " is not allowed!");
			System.exit(-2);
		} else {
			// Προσθήκη τιμής στο τοπικό HashMap για χρήση του από το symtable
			// στη συνέχεια
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

	// Μέθοδος που χρησιμοποιείται για ανάθεση λίστας σε μεταβλητή
	public void inAListExpression(AListExpression node) {
		// Όνομα λίστας
		String id = node.getId().getText();
		int line = node.getId().getLine();
		int pos = node.getId().getPos();

		// Έκφραση από την οποία θα προκύψει το μέγεθος της λίστας
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

				// Προσθήκη λίστας στο τοπικό HashTable το οποίο θα
				// χρησιμοποιηθεί
				// αργότερα από τον Πίνακα Συμβόλων
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

	// Μέθοδος που ελέγχει αν μια μεταβλητή έχει δηλωθεί διασχίζοντας τον κόμβο
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

	// Μέθοδος που χρησιμοποιείται για τις πράξεις με προθεματικούς και
	// μεταθεματικούς τελεστές σε λίστα
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
				// Έλεγχος του δείκτη και εμφάνιση σφάλματος σε περίπτωση που
				// υπερβεί το μέγεθος της λίστας
				int index = (int) val;
				if (index > list.size() || index < 0) {
					System.out.println("Index out of bounds: " + index + " out of list size " + list.size());
					System.exit(-4);
				} else {
					ArrayList prepostParams = new ArrayList<>();
					// Τιμή της λίστας στο στοιχείο index
					int listIndexValue = (int) ((ArrayList) list.get(index)).get(0);

					// Έλεγχος για το ποιος είναι ο παραπάνω κόμβος και εκτέλεση
					// της
					// αντίστοιχης πράξης
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

	// Μέθοδος που χρησιμοποιείται για τις πράξεις με προθεματικούς
	// και μεταθεματικούς τελεστές σε μεταβλητή
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
	 * Στα παρακάτω κομμάτια κώδικα διασχίζουμε κόμβους τύπου Comparison.
	 * 
	 * Συγκεκριμένα: Για όλους τους κόμβους σύγκρισης δηλαδή τους great, less,
	 * eq, noteq ελέγχουμε τις εκφράσεις για τις οποίες πραγματοποιείται
	 * σύγκριση και εμφανίζουμε μηνύματα σφάλματος όπου χρειάζεται. Πχ δε μπορεί
	 * να πραγματοποιηθεί σύγκριση ανάμεσα σε τύπους Integer και String.
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

		// Έλεγχος αν οι 2 εκφράσεις είναι του ίδιου τύπου
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
	 * Στα παρακάτω κομμάτια κώδικα διασχίζουμε κόμβους τύπου Number και String
	 * 
	 * Συγκεκριμένα: Παίρνουμε τις τιμές των κόμβων και τις παιρνάμε στον πατέρα
	 * κόμβο
	 * 
	 */
	public void inANumberValue(ANumberValue node) {
		node.getNumber().apply(this);
	}

	public void inAIntNumber(AIntNumber node) {
		// Ακέραια τιμή του κόμβου
		int value = Integer.valueOf(node.getInteger().getText());
		int line = node.getInteger().getLine();
		int pos = node.getInteger().getPos();

		// Λίστα που κρατάει τιμή, γραμμή και θέση του κόμβου
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
		// Συμβολοσειρά του κόμβου
		String value = node.getString().getText();
		value = value.replace("\"", "");
		int line = node.getString().getLine();
		int pos = node.getString().getPos();

		// Λίστα που κρατάει τιμή, γραμμή και θέση του κόμβου
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