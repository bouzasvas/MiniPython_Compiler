/*
 * 	-------Μέλη Ομάδας-------
 * 
 * Διακάκης Ελευθέριος - 3120036
 * Μπούζας Βασίλειος - 3120124
 * Ντούλος Ξενοφών - 3120133
 * Χρόνης Γεώργιος - 3120209
 * 
 */

/*				Έλεγχος Κλήσης Συνάρτησης
 * 
 *  Η κλάση αυτή ασχολείται με τον έλεγχο πιθανών σφαλμάτων που μπορούν να
 *  προκύψουν κατά την κλήση μιας συνάρτησης.
 *  
 *  Συγκεκριμένα κάνει Override τη μέθοδο inAFunctionCall η οποία ενεργοποιείται μόλις
 *  ανιχνευθεί στον πηγαίο κώδικα κομμάτι που αφορά την κλήση μιας συνάρτησης.
 *  
 *   Ελέγχει:
 *   	1. Την κλήση συνάρτησης που δεν έχει δηλωθεί
 *   	2. Την κλήση συνάρτησης με λάθος παραμέτρους από αυτές που έχουν δηλωθεί
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

		//	Έλεγχος αν έχει δηλωθεί η συνάρτηση που αφορά τη συγκεκριμένη κλήση
		if (!this.symtable.containsKey(callId)) {
			System.out.println(
					"Called function [" + callId + "] at line " + line + " at pos " + pos + " is not defined!");
			//	Σφάλμα εξόδου με κωδικό 3
			System.exit(-3);
		} else {
			//	Λίστα που περιέχει τις μεταβλητές της δηλωμένης συνάρτησης
			ArrayList STArgs = ((ArrayList) (((ArrayList) this.symtable.get(callId)).get(0)));
			
			//	Λίστα που περιέχει τις μεταβλητές της κληθείσας συνάρτησης
			ArrayList callArgs = null;
			
			//	Αριρθμός Παραμέτρων Δηλωμένης Συνάρτησης
			int numSTArgs = STArgs.size();
			//	Αριθμός Παραμέτρων που έχουν default τιμή
			int defArgs = 0;

			//	Υπολογισμός αριθμού προκαθορισμένων παραμέτρων
			for (int index = 0; index < numSTArgs; index++) {
				AbstractMap.SimpleEntry arg = (AbstractMap.SimpleEntry) STArgs.get(index);

				if (arg.getValue() != null) {
					defArgs++;
				}
			}

			//	Αριθμός παραμέτρων κληθείσας συνάρτησης
			int calledNumArgs = -1;
			
			//	Κόμβος που αφορά τη λίστα παραμέτρων της κληθείσας συνάρτησης
			PArgList arglist = node.getArgList();
			
			//	Διάσχιση Κόμβου
			arglist.apply(this);
			

			if (this.symtable.containsKey(arglist)) {
				callArgs = (ArrayList) this.symtable.get(arglist);
				//	Ανάθεση τιμής από το αποτέλεσμα της διάσχισης
				calledNumArgs = callArgs.size();
				this.symtable.remove(arglist);
			}

			//	Έλεγχος για λάθος κλήση συνάρτησης που αφορά τις παραμέτρους της
			/*	Αν ο αριθμός παραμέτρων της κληθείσας συνάρτησης > αριθμός παραμέτρων της δηλωμένης συνάρτησης
			 * 	ή αν ο αριθμός παραμέτρων της κλειθήσας < αριθμός παραμέτρων της δηλωμένης - αριθμός default παραμέτρων
			 * 	τότε εμφάνισε σφάλμα και τερμάτισε το πρόγραμμα.
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

	//	Visitor για τον κόμβο inAArgList - υπολογίζει τον αριθμό παραμέτρων της κληθείσας συνάρτησης	
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

	//	Visitor για τον κόμβο inAMoreExp
	public void inAMoreExp(AMoreExp node) {
		PExpression exp = node.getExpression();
		exp.apply(new CompleteSymbolsTable(symtable, localVars));
		
		if (this.localVars.containsKey(exp)) {
			this.localVars.put(node, this.localVars.get(exp));
		}
	}
}
