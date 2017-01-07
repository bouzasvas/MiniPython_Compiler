/*
 * 	-------Μέλη Ομάδας-------
 * 
 * Διακάκης Ελευθέριος - 3120036
 * Μπούζας Βασίλειος - 3120124
 * Ντούλος Ξενοφών - 3120133
 * Χρόνης Γεώργιος - 3120209
 * 
 */

/* 			H main Κλάση του Μεταγλωτιστή για τη γλώσσα MiniPython
 * 
 * Διαβάζει από τη γραμμή εντολών το αρχείο που περιέχει τον πηγαίο κώδικα της γλώσσας MiniPython
 * 
 * Αρχικοποιεί 2 Hashtable:
 * 		symtable: Ο πίνακας συμβόλων του Μεταγλωτιστή
 * 		localVars: Πίνακας που περιέχει προσωρινές μεταβλητές του προγράμματος και χρησιμοποιείται για την κατασκευή του Πίνακα Συμβόλων
 * 
 * Ενεργοποιεί τους 2 Visitors:
 * 		CompleteSymbolsTable.java: Η κλάση που γεμίζει τον πίνακα συμβόλων του Μεταγλωτιστή. Ακόμα ελέγχει για συντακτικά λάθη και εμφανίζει κατάλληλα
 * 									μηνύματα σφαλμάτων για να ενημερώσει τον χρήστη.
 * 
 * 		CheckFunctionCall.java: Η κλάση που ελέγχει την κλήση συναρτήσεων όπως πχ. Αν έχουν δηλωθεί, αν η κλήση γίνεται με τις σωστές παραμέτρους κτλ.
 * 								Ενεργοποιείται κατά τη 2η διάσχιση του AST.
 */

import java.io.*;
import minipython.lexer.Lexer;
import minipython.parser.Parser;
import minipython.node.*;
import java.util.*;

public class ParserTest {
	public static void main(String[] args) {
		try {
			Parser parser = new Parser(new Lexer(new PushbackReader(new FileReader(args[0].toString()), 1024)));

			Hashtable symtable = new Hashtable();
			Hashtable localVars = new Hashtable();
			Start ast = parser.parse();
			ast.apply(new CompleteSymbolsTable(symtable, localVars));
			ast.apply(new CheckFunctionCall(symtable, localVars));
		} catch (Exception e) {
			System.err.println(e);
		}
		finally {
			System.out.println("Compilation completed with no errors!");
		}
	}
}