// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS WriteCubicleFile                                                       *
*                                                                          *
* Contains the method Write for writing out a tokenized spec as a TLA      *
* file, deleting the "`^ ... ^'" parts of comments, and replacing "`~",    *
* "~'", "`.", and ".'" by spaces.                                          *
***************************************************************************/
package tla2sany.cubicle ;
import tla2sany.semantic.*;
import util.UniqueString;

import java.io.*;
import java.util.*;

public class WriteCubicleFile
 { public static void Write(String fileName, Vector <OpApplNode> opdefList, UniqueString[] varNames, HashMap <UniqueString, OpApplNode> hmap)
    {
	 try{
	 File file = new File(fileName);

     
     // creates the file
     file.createNewFile();
     
     // creates a FileWriter Object
     FileWriter writer = new FileWriter(file);
     
     // Writes the variables to the file
    /*for (int i=0; i<varNames.length; i++) {
        String var1 = "var "+varNames[i]+":"+varNames[i]+"1";
        writer.write(var1);
        writer.write("\n");
    }*/

     Set set = hmap.entrySet();
     Iterator iterator = set.iterator();
     while(iterator.hasNext()) {
         Map.Entry mentry = (Map.Entry)iterator.next();
         if (mentry.getValue() instanceof OpApplNode){

             OpApplNode node = (OpApplNode) mentry.getValue();// get setenumerate variable Cmessage i.e Coordinator \in Cmessage
             ExprOrOpArgNode[] argNode = node.getArgs();
             SymbolNode OpNode = node.getOperator();
             if (argNode.length == 0) {
                 if (OpNode instanceof OpDefNode)
                 {
                     SemanticNode expr = ((OpDefNode) OpNode).getBody();
                     OpApplNode expr1 = (OpApplNode) expr;
                     SymbolNode opNode = expr1.getOperator(); //$setenumerate
                     ExprOrOpArgNode[] exprOrOpArgNodes = expr1.getArgs();
                     String varList = SetEnumerators(exprOrOpArgNodes);
                    // String typeDecl = "type "+OpNode.getName()+"="+((OpDefNode) OpNode).getBody();
                     String typeDecl = "type "+OpNode.getName()+"="+varList;
                     String varDecl = "var "+mentry.getKey()+":"+OpNode.getName();
                     writer.write(typeDecl);
                     writer.write("\n");
                     writer.write(varDecl);
                     writer.write("\n");
                 }
                }
                if(argNode.length > 0) { //setFunction
                 if (OpNode.getName().equals("$SetOfFcns")){
                     ExprOrOpArgNode[] setFcns = node.getArgs();
                     ExprNode setf = (ExprNode) setFcns[0];
                     ExprNode setf1 = (ExprNode) setFcns[1];
                     if (setf1 instanceof OpApplNode){
                         OpApplNode node1 = (OpApplNode) setf1 ;
                         SymbolNode node2 = node1.getOperator();
                         if (node2 instanceof OpDefNode)
                         {
                             //ExprNode typemsg = ((OpDefNode) node2).getBody();
                             SemanticNode expr = ((OpDefNode) node2).getBody();
                             OpApplNode expr1 = (OpApplNode) expr;
                             SymbolNode opNode = expr1.getOperator(); //$setenumerate
                             ExprOrOpArgNode[] exprOrOpArgNodes = expr1.getArgs();
                             String varList = SetEnumerators(exprOrOpArgNodes);

                             String typeDecl = "type "+((OpApplNode) setf1).getOperator().getName()+"="+varList;
                             String arrDecl = "array "+ mentry.getKey()+"[proc]:"+ ((OpApplNode) setf1).getOperator().getName();
                             writer.write(typeDecl);
                             writer.write("\n");
                             writer.write(arrDecl);
                             writer.write("\n");
                         }

                     }
                 }
             }
         }

     }


     writer.flush();
     writer.close();
	 }
	 catch (IOException e) {

			e.printStackTrace();
		 
	 }

    }
     private static String SetEnumerators(ExprOrOpArgNode[] exprOrOpArgNodes) {
         String varList = "";
         for (int i = 0; i < exprOrOpArgNodes.length; i++) {
             StringNode    expr1  = (StringNode) exprOrOpArgNodes[i];
             if (i==0){
                 varList = varList.concat(String.valueOf(expr1.getRep()));

             }else {
                 varList = varList.concat("|"+String.valueOf(expr1.getRep()));

             }
         }
        return varList;
     }

 }  