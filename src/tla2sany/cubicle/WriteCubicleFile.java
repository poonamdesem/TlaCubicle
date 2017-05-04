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
import tlc2.output.EC;
import tlc2.value.StringValue;
import util.Assert;
import util.UniqueString;

import java.io.*;
import java.util.*;

public class WriteCubicleFile {
    public static void Write(String fileName, HashMap <UniqueString, OpApplNode> hmap, HashMap <UniqueString, ExprNode> initHmap, HashMap <UniqueString, OpApplNode> hnext, LevelNode levelNode) throws Exception {
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
                            String typeDecl = "type " + lowerFirstL(OpNode.getName()) + " = " + varList;
                            String varDecl = "var " + mentry.getKey() + ":" + lowerFirstL(OpNode.getName());
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
                                    if (expr != null) {
                                        OpApplNode expr1 = (OpApplNode) expr;
                                        ExprOrOpArgNode[] exprOrOpArgNodes = expr1.getArgs();
                                        String varList = SetEnumerators(exprOrOpArgNodes);
                                        String procList = getProcList(setf);
                                        String typeDecl = "type " + lowerFirstL(((OpApplNode) setf1).getOperator().getName()) + "=" + varList;
                                        String arrDecl = "array " + capitalizeFirstL(UniqueString.uniqueStringOf(mentry.getKey().toString())) + "[" + procList + "]:" + lowerFirstL(((OpApplNode) setf1).getOperator().getName());
                                        writer.write(typeDecl);
                                        writer.write("\n");
                                        writer.write(arrDecl);
                                        writer.write("\n");

                                    } else {
                                        throw new Exception("TypeOK invariant is not in required format");
                                        //Assert.fail(EC.TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM,"TypeOK invariant is not in required format");
                                    }

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
            writer.write("\n");
            //  Translation of Init section end here

            // Translation of Actions start here
            Set hActionset = hnext.entrySet();
            Iterator it = hActionset.iterator();
            String nextId = "";
            String nextParam = "";
            String param = "";
            String transitionparam="";
            String transitionparam1="";
            String actionName = "";
            String specvalues = "";
            String specvalues1 = "";
            UniqueString var = UniqueString.uniqueStringOf("");
            UniqueString val = UniqueString.uniqueStringOf("");
            UniqueString updatevar = UniqueString.uniqueStringOf("");
            UniqueString updateval = UniqueString.uniqueStringOf("");
            while (it.hasNext()) { // Iterate through the conjuct list of  Next
                Map.Entry me = (Map.Entry) it.next();
                OpApplNode opApplNode = (OpApplNode) me.getValue();
                ExprOrOpArgNode[] exprOrOpArgNode = opApplNode.getArgs();
                if (exprOrOpArgNode.length > 0) {

                    for (int l = 0; l < exprOrOpArgNode.length; l++) {
                        OpApplNode opApplNode1 = (OpApplNode) exprOrOpArgNode[l];
                        transitionparam = transitionparam.concat(String.valueOf(opApplNode1.getOperator().getName()) + ",");
                    }
                    transitionparam1 = transitionparam.substring(0,transitionparam.length()-1);
                    actionName = "transition " + me.getKey() + "(" + transitionparam1 + ")";


                } else {
                    actionName = "transition " + me.getKey() + "()";

                }
                writer.write(actionName);
                writer.write("\n");
                transitionparam="";
                HashMap <UniqueString, UniqueString> hmapUnprimed = new HashMap <>();
                HashMap <UniqueString, UniqueString> hactionmapPrimed = new HashMap <>();

                getActionVar(opApplNode, hmapUnprimed, hactionmapPrimed);
                Set set1 = hmapUnprimed.entrySet();

                Iterator iterator1 = set1.iterator();
                //  System.out.print(iterator.);
                String reqStmt = "";
                while (iterator1.hasNext()) {
                    Map.Entry mentry;
                    mentry = (Map.Entry) iterator1.next();
                    var = (UniqueString) mentry.getKey();
                    val = (UniqueString) mentry.getValue();
                    reqStmt = reqStmt + " && " + var + "=" + val;
                    //  System.out.println("key:"+mentry.getKey() + " value:" + mentry.getValue());
                }
                reqStmt = reqStmt.substring(4); //remove && from the begining of the require String
                writer.write("requires {" + reqStmt + "}");
                writer.write("\n");

                Set updateActionSet = hactionmapPrimed.entrySet();

                Iterator upit = updateActionSet.iterator();
                writer.write("{");
                writer.write("\n");
                while (upit.hasNext()) {
                    Map.Entry updateentry;
                    updateentry = (Map.Entry) upit.next();
                    updatevar = (UniqueString) updateentry.getKey();
                    updateval = (UniqueString) updateentry.getValue();
                    //   System.out.println("key:"+updatevar + " value:" + updateval);
                    writer.write(updatevar + ":=" + updateval + ";");
                    writer.write("\n");
                }
                writer.write("}");
                //writer.write("{" + updatevar + ":=" + updateval + ";}");
                writer.write("\n");
                writer.write("\n");
            }

            // Translation for unsafe state begin here
            if(levelNode!=null) {

                if (levelNode instanceof OpApplNode) {
                    OpApplNode node = (OpApplNode) levelNode;
                    FormalParamNode[][] formalParamNodes = node.getBdedQuantSymbolLists(); //get quantifier parameter rm
                    if (formalParamNodes != null) {
                        for (int j = 0; j < formalParamNodes[0].length; j++) {
                            SymbolNode symbolNode = formalParamNodes[0][j];
                            param = param.concat(String.valueOf(symbolNode.getName()) + ",");

                        }
                        String quantfParam = param.substring(0, param.length() - 1);
                        writer.write("unsafe(" + quantfParam + ")");
                        writer.write("\n");
                        writer.write("{");
                        writer.write("\n");
                    }
                    ExprOrOpArgNode[] args = node.getArgs();
                    ExprNode exprNode = (ExprNode) args[0];
                    if (exprNode instanceof OpApplNode) {
                        OpApplNode opApplNode = (OpApplNode) exprNode;
                        ExprNode exprNode1 = (ExprNode) opApplNode.getArgs()[0]; // get rid of negation
                        if (getVar(exprNode1).equals("$ConjList")) {
                            OpApplNode applNode = (OpApplNode) exprNode1;
                            ExprOrOpArgNode[] argNodes = applNode.getArgs();
                            for (int k = 0; k < argNodes.length; k++) {
                                OpApplNode conj = (OpApplNode) argNodes[k];
                                OpApplNode opApplNode1 = (OpApplNode) conj.getArgs()[0];
                                UniqueString val1 = getVar(conj.getArgs()[1]);
                                UniqueString vari = UniqueString.uniqueStringOf(processOperator(opApplNode1) + "=" + val1); // return variable name with parameter i.e rmState[rm]
                                specvalues = specvalues.concat(String.valueOf(vari) + " && ");
                            }
                            specvalues1 = specvalues.substring(0, specvalues.length() - 4);
                            writer.write(specvalues1);
                        }

                    }
                    writer.write("\n");

                    writer.write("}");
                    writer.write("\n");
                }
            }else{
                throw new Exception("Spec name is not correct/found");
            }

            // Translation for unsafe state end here

            writer.flush();
            writer.close();

        } catch (IOException e) {
            e.printStackTrace();

        } catch (Exception e) {
            e.printStackTrace();
        }

    }

    private static UniqueString processOperator(OpApplNode opApplNode1) {
        SymbolNode symbolNode = opApplNode1.getOperator();
        UniqueString opName = symbolNode.getName(); //get action variable name
        if (opName.equals("$FcnApply")) { //rmState[rm]
            ExprOrOpArgNode[] argNode = opApplNode1.getArgs();
            UniqueString unPrimedVar = getVar(argNode[0]);
            UniqueString unPrimedArg = getVar(argNode[1]);
            UniqueString unPrimedVariable = UniqueString.uniqueStringOf(unPrimedVar + "[" + unPrimedArg + "]");
            return unPrimedVariable;
        }
        return null;

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
                        if (conj.getArgs()[1] instanceof StringNode) {
                            //UniqueString primedValue = UniqueString.uniqueStringOf(String.valueOf(getStringVal(conj.getArgs()[1] )));
                            UniqueString primedValue = getVar(conj.getArgs()[1]);
                            hactionmapPrimed.put(primedVar, primedValue);
                        }
                        if (conj.getArgs()[1] instanceof OpApplNode) {
                            OpApplNode actionValue = (OpApplNode) conj.getArgs()[1];
                            UniqueString primedValue = getVar(actionValue);
                            if (primedValue.equals("$Except")) {
                                ExprOrOpArgNode[] primedArgs = actionValue.getArgs();
                                if (getVar(primedArgs[1]).equals("$Pair")) {
                                    OpApplNode opApplNode11 = (OpApplNode) primedArgs[1];
                                    ExprOrOpArgNode[] exprOrOpArgNode = opApplNode11.getArgs();
                                    OpApplNode opApplNode2 = (OpApplNode) exprOrOpArgNode[0];
                                    ExprOrOpArgNode[] exprOrOpArgNode1 = opApplNode2.getArgs(); // get parameter in Except
                                    //  System.out.println("var==="+getVar(exprOrOpArgNode1[0]));
                                    //  System.out.println("value==="+getVar(exprOrOpArgNode[1]));
                                    UniqueString primedVariable = UniqueString.uniqueStringOf(primedVar + "[" + getVar(exprOrOpArgNode1[0]) + "]");
                                    hactionmapPrimed.put(primedVariable, getVar(exprOrOpArgNode[1]));

                                }

                            }
                        }

                    }
                    if (opName.equals("$FcnApply")) { //rmState[rm]
                        ExprOrOpArgNode[] argNode = opApplNode1.getArgs();
                        UniqueString unPrimedVar = getVar(argNode[0]);
                        UniqueString unPrimedArg = getVar(argNode[1]);
                        UniqueString unPrimedVariable = UniqueString.uniqueStringOf(unPrimedVar + "[" + unPrimedArg + "]");
                        hmapUnprimed.put(unPrimedVariable, getVar(conj.getArgs()[1]));
                    }
                    if (opName.equals("\\in")) {                         //forall_other rm. (State[rm] = ProposeCommit)
                        ExprOrOpArgNode[] argNode = opApplNode1.getArgs();
                        OpApplNode opApplNode11 = (OpApplNode) argNode[0]; //(State[rm] = ProposeCommit)
                        ExprOrOpArgNode[] argNode1 = opApplNode11.getArgs();
                        OpApplNode opApplNode12 = (OpApplNode) argNode1[0]; //State
                        OpApplNode opApplNode13 = (OpApplNode) argNode1[1]; //rm
                        UniqueString primedVar = getVar(opApplNode12);
                        UniqueString primedVar1 = getVar(opApplNode13);
                        UniqueString unPrimedVariable = UniqueString.uniqueStringOf("forall_other " + primedVar1 + ".(" + primedVar + "[" + primedVar1 + "]");
                        OpApplNode opNode1 = ((OpApplNode) argNode[1]);
                        ExprOrOpArgNode[] exp = opNode1.getArgs();
                        hmapUnprimed.put(unPrimedVariable, getVar(exp[0]).concat(UniqueString.uniqueStringOf(")")));

                    }

                }

            }

        } else {
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
        if (node instanceof StringNode) {
            StringNode expr1 = (StringNode) node;
            StringValue val = new StringValue(expr1.getRep()); // String value returns string with double quotes
            String val1 = String.valueOf(val).replace("\"", "");
            UniqueString value = UniqueString.uniqueStringOf(String.valueOf(val1));
            return value;

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
               // varList = varList.concat(String.valueOf(expr1.getRep()));
                varList = varList.concat(String.valueOf(capitalizeFirstL(expr1.getRep())));


            } else {
                varList = varList.concat(" | " + String.valueOf(capitalizeFirstL(expr1.getRep())));
            }
        }
        return varList;
    }

    private static String capitalizeFirstL(UniqueString rep) {
        if(rep!=null){
            String output = rep.toString().substring(0, 1).toUpperCase() + rep.toString().substring(1);
            return  output;

        }
        return null;
    }
    private static String lowerFirstL(UniqueString rep) {
        if(rep!=null){
            String output = rep.toString().substring(0, 1).toLowerCase() + rep.toString().substring(1);
            return  output;

        }
        return null;
    }
}