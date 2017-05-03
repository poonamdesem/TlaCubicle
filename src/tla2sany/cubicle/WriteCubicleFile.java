// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
 * CLASS WriteCubicleFile                                                       *
 *                                                                          *
 * Contains the method Write for writing out a tokenized spec as a TLA      *
 * file, deleting the "`^ ... ^'" parts of comments, and replacing "`~",    *
 * "~'", "`.", and ".'" by spaces.                                          *
 ***************************************************************************/
package tla2sany.cubicle;

import tla2sany.semantic.*;
import tlc2.value.StringValue;
import util.UniqueString;

import java.io.*;
import java.util.*;

public class WriteCubicleFile {
    public static void Write(String fileName, HashMap <UniqueString, OpApplNode> hmap, HashMap <UniqueString, ExprNode> initHmap, HashMap <UniqueString, OpApplNode> hnext) {
        try {
            File file = new File(fileName);
            // creates the file
            file.createNewFile();
            // creates a FileWriter Object
            FileWriter writer = new FileWriter(file);
            Set set = hmap.entrySet();
            Iterator iterator = set.iterator();
            while (iterator.hasNext()) { // list of conjuct in TypeOK invariant
                Map.Entry mentry = (Map.Entry) iterator.next();
                if (mentry.getValue() instanceof OpApplNode) {

                    OpApplNode node = (OpApplNode) mentry.getValue();// get setenumerate variable Cmessage i.e Coordinator \in Cmessage
                    ExprOrOpArgNode[] argNode = node.getArgs();
                    SymbolNode OpNode = node.getOperator();
                    if (argNode.length == 0) {
                        if (OpNode instanceof OpDefNode) {
                            SemanticNode expr = ((OpDefNode) OpNode).getBody();
                            OpApplNode expr1 = (OpApplNode) expr;
                            SymbolNode opNode = expr1.getOperator(); //$setenumerate
                            ExprOrOpArgNode[] exprOrOpArgNodes = expr1.getArgs();
                            String varList = SetEnumerators(exprOrOpArgNodes);
                            String typeDecl = "type " + OpNode.getName() + "=" + varList;
                            String varDecl = "var " + mentry.getKey() + ":" + OpNode.getName();
                            writer.write(typeDecl);
                            writer.write("\n");
                            writer.write(varDecl);
                            writer.write("\n");
                        }
                    }
                    if (argNode.length > 0) { //setFunction
                        if (OpNode.getName().equals("$SetOfFcns")) {
                            ExprOrOpArgNode[] setFcns = node.getArgs();
                            ExprNode setf = (ExprNode) setFcns[0]; // times
                            ExprNode setf1 = (ExprNode) setFcns[1]; //$setenumerate
                            if (setf1 instanceof OpApplNode) {
                                OpApplNode node1 = (OpApplNode) setf1;

                                SymbolNode node2 = node1.getOperator();
                                if (node2 instanceof OpDefNode) {

                                    SemanticNode expr = ((OpDefNode) node2).getBody();
                                    OpApplNode expr1 = (OpApplNode) expr;
                                    ExprOrOpArgNode[] exprOrOpArgNodes = expr1.getArgs();
                                    String varList = SetEnumerators(exprOrOpArgNodes);
                                    String procList = getProcList(setf);
                                    String typeDecl = "type " + ((OpApplNode) setf1).getOperator().getName() + "=" + varList;
                                    String arrDecl = "array " + mentry.getKey() + "[" + procList + "]:" + ((OpApplNode) setf1).getOperator().getName();
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
            String strTowrite = "";
            String strTowrite1 = "";
            String initParam = "";
            String initParam1 = "";

            HashMap collectInitVar = new HashMap();
            Set initSet = initHmap.entrySet();
            Iterator initIt = initSet.iterator();
            while (initIt.hasNext()) { // list of conjuct in Init
                Map.Entry mentry = (Map.Entry) initIt.next();
                objVal = mentry.getValue();
                objKey = mentry.getKey();
                if (mentry.getValue() instanceof OpApplNode) { // for function
                    OpApplNode node1 = (OpApplNode) mentry.getValue(); //get function
                    SymbolNode node2 = node1.getOperator(); //$FcnConstructor
                    FormalParamNode[][] formalParamNodes = node1.getBdedQuantSymbolLists();
                    String initId = "";
                    for (int j = 0; j < formalParamNodes[0].length; j++) {
                        SymbolNode symbolNode = (SymbolNode) formalParamNodes[0][j];
                        collectInitVar.put(symbolNode.getName(), symbolNode.getName());
                        initId = initId.concat(String.valueOf(symbolNode.getName()) + ",");
                    }
                    if (initId != null) {
                        initParam = initId.substring(0, initId.length() - 1);
                    }
                }

                strTowrite = strTowrite.concat(getInitList(objVal, objKey, initParam));
                strTowrite1 = strTowrite.substring(0, strTowrite.length() - 3); // removing && at the end

            }
            Set hset = collectInitVar.entrySet();
            Iterator i = hset.iterator();
            // Display elements
            while (i.hasNext()) {
                Map.Entry me = (Map.Entry) i.next();
                initStr = initStr.concat(me.getValue() + ",");
            }
            if (!hset.isEmpty()) {
                initParam1 = initStr.substring(0, initStr.length() - 1);
                initStr = "init(" + initParam1 + "){";
            } else {
                initStr = "init{";

            }
            writer.write("\n");
            writer.write(initStr); // write init()

            writer.write(strTowrite1);

            writer.write("}");
            writer.write("\n");
            writer.write("\n"); //  Translation of Init section end here

            // Translation of Actions start here
            Set hActionset = hnext.entrySet();
            Iterator it = hActionset.iterator();
            String nextId = "";
            String nextParam = "";
            String actionName = "";
            UniqueString var = UniqueString.uniqueStringOf("");
            UniqueString val = UniqueString.uniqueStringOf("");
            UniqueString updatevar = UniqueString.uniqueStringOf("");
            UniqueString updateval = UniqueString.uniqueStringOf("");
            while (it.hasNext()) {
                Map.Entry me = (Map.Entry) it.next();
                OpApplNode opApplNode = (OpApplNode) me.getValue();
                ExprOrOpArgNode[] exprOrOpArgNode = opApplNode.getArgs();

                if (exprOrOpArgNode.length > 0) {
                    for (int l = 0; l < exprOrOpArgNode.length; l++) {
                        OpApplNode opApplNode1 = (OpApplNode) exprOrOpArgNode[l];
                        actionName = "transition " + me.getKey() + "(" + opApplNode1.getOperator().getName() + ")";
                    }
                } else {
                    actionName = "transition " + me.getKey() + "()";

                }
                writer.write(actionName);
                writer.write("\n");

                HashMap <UniqueString, UniqueString> hmapUnprimed = new HashMap <>();
                HashMap <UniqueString, UniqueString> hactionmapPrimed = new HashMap <>();

                getActionVar(opApplNode, hmapUnprimed,hactionmapPrimed);
                Set set1 = hmapUnprimed.entrySet();

                Iterator iterator1 = set1.iterator();
                while (iterator1.hasNext()) {
                    Map.Entry mentry;
                    mentry = (Map.Entry) iterator1.next();
                    var = (UniqueString) mentry.getKey();
                    val = (UniqueString) mentry.getValue();

                    //System.out.print(mentry.getKey() + " " + mentry.getValue());

                }
                writer.write("requires {" + var + "=" + val + "}");
                writer.write("\n");

                Set updateActionSet = hactionmapPrimed.entrySet();

                Iterator upit = updateActionSet.iterator();
                while (upit.hasNext()) {
                    Map.Entry updateentry;
                    updateentry = (Map.Entry) upit.next();
                    updatevar = (UniqueString) updateentry.getKey();
                    updateval = (UniqueString) updateentry.getValue();

                }
                writer.write("{" + updatevar + ":=" + updateval + ";}");
                writer.write("\n");
                writer.write("\n");

                // {State[rm] := Abort;}


            }

            writer.flush();
            writer.close();

        } catch (IOException e) {
            e.printStackTrace();

        } catch (Exception e) {
            e.printStackTrace();
        }

    }

    private static void getActionVar(OpApplNode opApplNode, HashMap <UniqueString, UniqueString> hmapUnprimed, HashMap <UniqueString, UniqueString> hactionmapPrimed) throws Exception {
        // if(opApplNode.getOperator().getName().equals("Commit")){
       // System.out.println("In Action===" + opApplNode.getOperator().getName());
        if (opApplNode != null) {

            SymbolNode opNode = opApplNode.getOperator();
            if (opNode instanceof OpDefNode) {
                OpDefNode defNode = (OpDefNode) opNode;
                LevelNode node = defNode.getBody();
                OpApplNode node1 = (OpApplNode) node;
                ExprOrOpArgNode[] args = node1.getArgs();
                for (int i = 0; i < args.length; i++) { // list of conjunction in action
                    OpApplNode conj = (OpApplNode) args[i];
                    OpApplNode opApplNode1 = (OpApplNode) conj.getArgs()[0];
                    SymbolNode symbolNode = opApplNode1.getOperator();
                    UniqueString opName = symbolNode.getName(); //get action variable name
                    // System.out.println(symbolNode.getArity());
                    if (symbolNode.getArity() == 0) {
                        //hmapUnprimed.put(opName, String.valueOf(getStringVal(conj.getArgs()[1])));
                        hmapUnprimed.put(opName, getVar(conj.getArgs()[1]));

                    }
                    if (opName.equals("'")) { // for primed action
                        OpApplNode actionVar = (OpApplNode) conj.getArgs()[0];
                        UniqueString primedVar = getVar(actionVar.getArgs()[0]);
                        if(conj.getArgs()[1] instanceof StringNode){
                            //UniqueString primedValue = UniqueString.uniqueStringOf(String.valueOf(getStringVal(conj.getArgs()[1] )));
                            UniqueString primedValue = getVar(conj.getArgs()[1]);
                            hactionmapPrimed.put(primedVar,primedValue);
                        }
                        if(conj.getArgs()[1] instanceof OpApplNode){
                            OpApplNode actionValue = (OpApplNode) conj.getArgs()[1];
                            UniqueString primedValue = getVar(actionValue);
                            if (primedValue.equals("$Except")) {
                                ExprOrOpArgNode[] primedArgs = actionValue.getArgs();
                                if(getVar(primedArgs[1]).equals("$Pair")){
                                    OpApplNode opApplNode11 = (OpApplNode) primedArgs[1];
                                    ExprOrOpArgNode[] exprOrOpArgNode = opApplNode11.getArgs();
                                    OpApplNode opApplNode2 = (OpApplNode) exprOrOpArgNode[0];
                                    ExprOrOpArgNode[] exprOrOpArgNode1 = opApplNode2.getArgs(); // get parameter in Except
                                  //  System.out.println("var==="+getVar(exprOrOpArgNode1[0]));
                                  //  System.out.println("value==="+getVar(exprOrOpArgNode[1]));
                                    UniqueString primedVariable = UniqueString.uniqueStringOf(primedVar+"["+getVar(exprOrOpArgNode1[0])+"]");
                                    hactionmapPrimed.put(primedVariable,getVar(exprOrOpArgNode[1]));

                                }

                            }
                        }

                    }
                    if (opName.equals("$FcnApply")) { //rmState[rm]
                        ExprOrOpArgNode[] argNode = opApplNode1.getArgs();
                        UniqueString unPrimedVar = getVar(argNode[0]);
                        UniqueString unPrimedArg = getVar(argNode[1]);
                        UniqueString unPrimedVariable = UniqueString.uniqueStringOf(unPrimedVar+"["+unPrimedArg+"]");
                        hmapUnprimed.put(unPrimedVariable,getVar(conj.getArgs()[1]));
                    }
                    if (opName.equals("\\in")) {                         //forall_other rm. (State[rm] = ProposeCommit)
                        ExprOrOpArgNode[] argNode = opApplNode1.getArgs();
                        OpApplNode opApplNode11 = (OpApplNode) argNode[0]; //(State[rm] = ProposeCommit)
                        ExprOrOpArgNode[] argNode1 = opApplNode11.getArgs();
                        OpApplNode opApplNode12 = (OpApplNode) argNode1[0]; //State
                        OpApplNode opApplNode13 = (OpApplNode) argNode1[1]; //rm
                        UniqueString primedVar = getVar(opApplNode12);
                        UniqueString primedVar1 = getVar(opApplNode13);
                        UniqueString unPrimedVariable = UniqueString.uniqueStringOf("forall_other "+primedVar1+".("+primedVar+"["+primedVar1+"]");
                        OpApplNode opNode1 = ((OpApplNode) argNode[1]);
                        ExprOrOpArgNode[] exp = opNode1.getArgs();
                        hmapUnprimed.put(unPrimedVariable, getVar(exp[0]).concat(UniqueString.uniqueStringOf(")")));

                    }

               /* ExprOrOpArgNode[] actionArgs =conj.getArgs();
                for (int j=0;j<actionArgs.length;j++){
                     OpApplNode actionVars = (OpApplNode) actionArgs[i]; //get primed variables
                     SymbolNode symbolNode1= actionVars.getOperator();
                     UniqueString opName1 = symbolNode.getName();
                     //System.out.println("body="+actionVars.getArgs().length);
                    if(opName.equals("'")){
                        UniqueString primedVar = getVar(actionVars.getArgs()[0]);
                    }

                 } */
                }

            }

        }
        else {
            throw new Exception("opApplNode is empty: " + opApplNode.getOperator().getName());
        }

        //}

    }

    private static UniqueString getVar(SemanticNode node) {
        //System.out.println("node=="+node);

        if (node instanceof OpApplNode) {
            SymbolNode opNode = ((OpApplNode) node).getOperator();
            return opNode.getName();

        }
        if(node instanceof StringNode){
            StringNode expr1 = (StringNode) node;
            StringValue val = new StringValue(expr1.getRep());
            UniqueString value = UniqueString.uniqueStringOf(String.valueOf(val));

            return value;

        }


        //UniqueString primedValue = UniqueString.uniqueStringOf(String.valueOf(getStringVal(conj.getArgs()[1] )));

        return null;

    }
    private static UniqueString getStringVal(SemanticNode node) {

        if(node instanceof StringNode){
            StringNode expr1 = (StringNode) node;
            StringValue val = new StringValue(expr1.getRep());
            return null;

        }
        return null;

    }

    private static String getInitList(Object objVal, Object objKey, String initParam) {

        if (objVal instanceof StringNode) {
            StringNode stringNode = (StringNode) objVal;
            String initStr1 = objKey + "=" + stringNode.getRep() + " && ";
            return initStr1;
        }
        if (objVal instanceof OpApplNode) { // for function
            OpApplNode node1 = (OpApplNode) objVal; //get function
            SymbolNode node2 = node1.getOperator(); //$FcnConstructor
            ExprOrOpArgNode[] setFcns = node1.getArgs();
            ExprNode setf = (ExprNode) setFcns[0];
            StringNode stringNode = (StringNode) setf;// get value i.e "working"
            String initStr1 = objKey + "[" + initParam + "]=" + stringNode.getRep() + " && ";
            return initStr1;
        } else {
            return null;
        }
    }

    private static String getProcList(ExprNode setf) {
        if (setf instanceof OpApplNode) {
            OpApplNode node3 = (OpApplNode) setf;
            ExprOrOpArgNode[] args = node3.getArgs();
            String procArr = "";

            int len = args.length;
            do {
                procArr = procArr.concat("proc,");
                len--;
            } while (len > 0);
            String str = procArr.substring(0, procArr.length() - 1); // removing , at the end
            return str;
        } else {
            return null;
        }
    }

    private static String SetEnumerators(ExprOrOpArgNode[] exprOrOpArgNodes) {
        String varList = "";
        for (int i = 0; i < exprOrOpArgNodes.length; i++) {
            StringNode expr1 = (StringNode) exprOrOpArgNodes[i];
            if (i == 0) {
                varList = varList.concat(String.valueOf(expr1.getRep()));

            } else {
                varList = varList.concat("|" + String.valueOf(expr1.getRep()));
            }
        }
        return varList;
    }

}