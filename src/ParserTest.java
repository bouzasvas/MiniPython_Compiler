/*
 * 	-------���� ������-------
 * 
 * �������� ���������� - 3120036
 * ������� ��������� - 3120124
 * ������� ������� - 3120133
 * ������ �������� - 3120209
 * 
 */

/* 			H main ����� ��� ������������ ��� �� ������ MiniPython
 * 
 * �������� ��� �� ������ ������� �� ������ ��� �������� ��� ������ ������ ��� ������� MiniPython
 * 
 * ����������� 2 Hashtable:
 * 		symtable: � ������� �������� ��� ������������
 * 		localVars: ������� ��� �������� ���������� ���������� ��� ������������ ��� ��������������� ��� ��� ��������� ��� ������ ��������
 * 
 * ����������� ���� 2 Visitors:
 * 		CompleteSymbolsTable.java: � ����� ��� ������� ��� ������ �������� ��� ������������. ����� ������� ��� ���������� ���� ��� ��������� ���������
 * 									�������� ��������� ��� �� ���������� ��� ������.
 * 
 * 		CheckFunctionCall.java: � ����� ��� ������� ��� ����� ����������� ���� ��. �� ����� �������, �� � ����� ������� �� ��� ������ ����������� ���.
 * 								�������������� ���� �� 2� �������� ��� AST.
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