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
import tla2tex.Symbol;
import util.UniqueString;

import java.io.*;
import java.util.*;

public class WriteCubicleFile
 { public static void Write(String fileName,HashMap <UniqueString, OpApplNode> hmap, HashMap <UniqueString, ExprNode> initHmap)
    {
	 try{
	 File file = new File(fileName);
     // creates the file
     file.createNewFile();
     // creates a FileWriter Object
     FileWriter writer = new FileWriter(file);
     Set set = hmap.entrySet();
     Iterator iterator = set.iterator();
     while(iterator.hasNext()) { // list of conjuct in TypeOK invariant
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
                     ExprNode setf = (ExprNode) setFcns[0]; // times
                     ExprNode setf1 = (ExprNode) setFcns[1]; //$setenumerate
                     if (setf1 instanceof OpApplNode){
                         OpApplNode node1 = (OpApplNode) setf1 ;

                         SymbolNode node2 = node1.getOperator();
                         if (node2 instanceof OpDefNode)
                         {

                             SemanticNode expr = ((OpDefNode) node2).getBody();
                             OpApplNode expr1 = (OpApplNode) expr;
                             ExprOrOpArgNode[] exprOrOpArgNodes = expr1.getArgs();
                             String varList = SetEnumerators(exprOrOpArgNodes);
                             String procList = getProcList(setf);
                             String typeDecl = "type "+((OpApplNode) setf1).getOperator().getName()+"="+varList;
                             String arrDecl = "array "+ mentry.getKey()+"["+procList+"]:"+ ((OpApplNode) setf1).getOperator().getName();
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
     // Translation of Init section start here
         String initStr = "";
         //writer.write(initStr);
         Object objVal = null;
         Object objKey = null;
         String strTowrite="";
         String strTowrite1="";
         String initParam="";
         String initParam1="";
         HashMap collectInitVar = new HashMap();
         Set initSet = initHmap.entrySet();
         Iterator initIt = initSet.iterator();
         while(initIt.hasNext()) { // list of conjuct in Init
             Map.Entry mentry = (Map.Entry) initIt.next();
             objVal =mentry.getValue();
             objKey =mentry.getKey();
             if (mentry.getValue() instanceof OpApplNode) { // for function
                 OpApplNode node1 = (OpApplNode) mentry.getValue(); //get function
                 SymbolNode node2 = node1.getOperator(); //$FcnConstructor
                 FormalParamNode[][] formalParamNodes = node1.getBdedQuantSymbolLists();
                 String initId = "";
                // for(int i=0;i<=formalParamNodes[0].length;i++) {
                     for (int j = 0; j < formalParamNodes[0].length; j++) {
                         SymbolNode symbolNode = (SymbolNode) formalParamNodes[0][j];
                         collectInitVar.put(symbolNode.getName(),symbolNode.getName());
                         initId = initId.concat(String.valueOf(symbolNode.getName()) + ",");
                     }
                 // }
                if (initId!=null){
                     initParam = initId.substring(0, initId.length()-1);
                    // initStr = "init("+initParam+"){";

                 }

                /* ExprOrOpArgNode[] setFcns = node1.getArgs();
                 ExprNode setf = (ExprNode) setFcns[0];
                 StringNode stringNode=(StringNode)setf;// get value i.e "working"
                 ExprNode[] exprNodes = node1.getBdedQuantBounds();
                 if (exprNodes[0] instanceof OpApplNode) { // getting RM
                     OpApplNode node3 = (OpApplNode) exprNodes[0];
                     System.out.println("expr  "+node3.getOperator().getName());

                 }
                 if (node2 instanceof OpDefNode) {
                     System.out.println("in if");
                     OpDefNode opDef1 = (OpDefNode) node2;
                     SymbolNode exprNode = (SymbolNode) opDef1;
                    System.out.println(exprNode.getName());

                }
                 String initStr1 = mentry.getKey()+"="+stringNode.getRep();
                 writer.write("\n");
                 writer.write(initStr1);*/

             }

             strTowrite =  strTowrite.concat(getInitList(objVal,objKey,initParam));
             strTowrite1 = strTowrite.substring(0, strTowrite.length()-3); // removing && at the end

         }
         Set hset = collectInitVar.entrySet();
         Iterator i = hset.iterator();
         // Display elements
         while(i.hasNext()) {
             Map.Entry me = (Map.Entry)i.next();
             initStr = initStr.concat(me.getValue() + ",");
         }
         if(!hset.isEmpty()){
             initParam1 = initStr.substring(0, initStr.length()-1);
             initStr = "init("+initParam1+"){";
         }else {
             initStr = "init{";

         }

         writer.write(initStr); // write init()

         writer.write(strTowrite1);

         writer.write("}");
         writer.write("\n");

     writer.flush();
     writer.close();

	 }
	 catch (IOException e) {
			e.printStackTrace();
		 
	 }

    }

     private static String getInitList(Object objVal, Object objKey,String initParam) {

         if(objVal instanceof StringNode){
             StringNode stringNode = (StringNode) objVal;
             String initStr1 = objKey+"="+stringNode.getRep()+" && ";
             return  initStr1;
         }
         if (objVal instanceof OpApplNode) { // for function
             OpApplNode node1 = (OpApplNode) objVal; //get function
             SymbolNode node2 = node1.getOperator(); //$FcnConstructor
             ExprOrOpArgNode[] setFcns = node1.getArgs();
             ExprNode setf = (ExprNode) setFcns[0];
             StringNode stringNode=(StringNode)setf;// get value i.e "working"
             String initStr1 = objKey+"["+initParam+"]="+stringNode.getRep()+" && ";
            return initStr1;
         } else{
             return  null;
         }
     }

     private static String getProcList(ExprNode setf) {
         if (setf instanceof OpApplNode) {
             OpApplNode node3 = (OpApplNode) setf;
             ExprOrOpArgNode[] args = node3.getArgs();
             String procArr="";

            int len = args.length;
             do {
                 procArr=procArr.concat("proc,");
                 len--;
             } while (len>0);
             String str = procArr.substring(0, procArr.length()-1); // removing , at the end
             return str;
         }

         else {
             return null;
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