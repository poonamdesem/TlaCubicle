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
            file.createNewFile(); // creates the file
            FileWriter writer = new FileWriter(file);// creates a FileWriter Object
            // Translation of TypeOK section end here

            /*In cubicle translation, variable, array declaration and assigning values to them is done from the TypeOK invariant of Spec.
            As cubicle is syntactically restricted We have to follow the some orders and rules. All the type declaration should be done first
            before use. In below code, hmap is a hashset which contains the variable and value of TypeOK invariant in key and value respectively.
            So, hmap sets iterated twice here. In first iteration it will generate type declaration and then it will assign that type to respective array
            or var in second iteration.
             */

            Set set = hmap.entrySet(); //set for array or var declaration
            Iterator iterator = set.iterator();
            Set typeset = hmap.entrySet(); //set for type declaration
            Iterator typeit = typeset.iterator();
            while (typeit.hasNext()) { // list of conjuct in TypeOK invariant for type declaration
                Map.Entry mentry = (Map.Entry) typeit.next();
                if (mentry.getValue() instanceof OpApplNode) {
                    OpApplNode node = (OpApplNode) mentry.getValue();// get setenumerate variable Cmessage i.e Coordinator \in Cmessage
                    SymbolNode OpNode = node.getOperator();
                    ExprOrOpArgNode[] argNode = node.getArgs();
                    if (argNode.length == 0) {
                        if (OpNode instanceof OpDefNode) {
                            SemanticNode expr = ((OpDefNode) OpNode).getBody();
                            OpApplNode expr1 = (OpApplNode) expr;
                            ExprOrOpArgNode[] exprOrOpArgNodes = expr1.getArgs();//$setenumerate
                            String varList = SetEnumerators(exprOrOpArgNodes);
                            String typeDecl = "type " + lowerFirstL(OpNode.getName()) + " = " + varList;
                            writer.write(typeDecl);
                            writer.write("\n");
                        }
                    }
                    if (argNode.length > 0) { //setFunction
                        if (OpNode.getName().equals("$SetOfFcns")) {
                            ExprOrOpArgNode[] setFcns = node.getArgs();
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
                                        String typeDecl = "type " + lowerFirstL(((OpApplNode) setf1).getOperator().getName()) + "=" + varList;
                                        writer.write(typeDecl);
                                        writer.write("\n");
                                        writer.write("\n");

                                    } else {
                                        throw new Exception("TypeOK invariant is not in required format");
                                    }

                                }

                            }
                        }
                    }
                }

            }
            while (iterator.hasNext()) { // list of conjuct in TypeOK invariant for var or array declaration
                Map.Entry mentry = (Map.Entry) iterator.next();
                if (mentry.getValue() instanceof OpApplNode) {
                    OpApplNode node = (OpApplNode) mentry.getValue();// get setenumerate variable Cmessage i.e Coordinator \in Cmessage
                    ExprOrOpArgNode[] argNode = node.getArgs();
                    SymbolNode OpNode = node.getOperator();
                    if (argNode.length == 0) {
                        if (OpNode instanceof OpDefNode) {
                            SemanticNode expr = ((OpDefNode) OpNode).getBody();
                            String varDecl = "var " + mentry.getKey() + ":" + lowerFirstL(OpNode.getName());
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
                            String procList = getProcList(setf);
                            String arrDecl = "array " + capitalizeFirstL(UniqueString.uniqueStringOf(mentry.getKey().toString())) + "[" + procList + "]:" + lowerFirstL(((OpApplNode) setf1).getOperator().getName());
                            writer.write("\n");
                            writer.write(arrDecl);
                            writer.write("\n");
                        }
                    }
                }

            }
            // Translation of TypeOK section end here

            // Translation of Init section start here
            String initStr = "";
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
                    UniqueString node2 = node1.getOperator().getName(); //$FcnConstructor
                    if(node2.equals("$FcnConstructor")){
                        FormalParamNode[][] formalParamNodes = node1.getBdedQuantSymbolLists();
                        String initId = "";
                        for (int j = 0; j < formalParamNodes[0].length; j++) {
                            SymbolNode symbolNode = formalParamNodes[0][j];
                            collectInitVar.put(symbolNode.getName(), symbolNode.getName());
                            initId = initId.concat(String.valueOf(symbolNode.getName()).toLowerCase() + ",");
                        }
                        if (initId != null) {
                            initParam = initId.substring(0, initId.length() - 1);
                        }
                    }


                }

                if(getInitList(objVal, objKey, initParam)!=null){
                    strTowrite = strTowrite.concat(getInitList(objVal, objKey, initParam)); //getInitList return init's values list i.e coordinator = Init
                    strTowrite1 = strTowrite.substring(0, strTowrite.length() - 3); // removing && at the end
                }
                else{
                    throw new Exception("Init is not in required format, value should be FuncConstructor or String");
                }


            }
            Set hset = collectInitVar.entrySet();
            Iterator i = hset.iterator();
            // Display elements
            while (i.hasNext()) {
                Map.Entry me = (Map.Entry) i.next();
                initStr = initStr.concat(me.getValue().toString().toLowerCase() + " ");
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

            // Translation for unsafe state begin here
            if (levelNode != null) {
                String specvalues = "";
                String specvalues1 = "";
                String param = "";
                if (levelNode instanceof OpApplNode) {
                    OpApplNode node = (OpApplNode) levelNode;
                    FormalParamNode[][] formalParamNodes = node.getBdedQuantSymbolLists(); //get quantifier parameter rm
                    if (formalParamNodes != null) {
                        for (int j = 0; j < formalParamNodes[0].length; j++) {
                            SymbolNode symbolNode = formalParamNodes[0][j];
                            param = param.concat(String.valueOf(symbolNode.getName()).toLowerCase() + " ");

                        }
                       // String quantfParam = param.substring(0, param.length() - 1);
                        writer.write("unsafe(" + param + ")");
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
                                UniqueString vari = UniqueString.uniqueStringOf(processOperator(opApplNode1)+ "=" + capitalizeFirstL(val1)); // return variable name with parameter i.e rmState[rm]
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
            } else {
                throw new Exception("Spec name is not correct/found");
            }

            // Translation for unsafe state end here

            // Translation of Actions start here
            Set hActionset = hnext.entrySet();
            Iterator it = hActionset.iterator();
            String nextId = "";
            String nextParam = "";
            String transitionparam = "";
            String transitionparam1 = "";
            String actionName = "";

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
                        transitionparam = transitionparam.concat(String.valueOf(opApplNode1.getOperator().getName()).toLowerCase() + " ");
                    }
                    transitionparam1 = transitionparam.substring(0, transitionparam.length() - 1);
                    actionName = "transition " + me.getKey() + "(" + transitionparam1 + ")";


                } else {
                    actionName = "transition " + me.getKey() + "()";

                }
                writer.write(actionName);
                writer.write("\n");
                transitionparam = "";
                HashMap <UniqueString, UniqueString> hmapUnprimed = new HashMap <>();
                HashMap <UniqueString, UniqueString> hactionmapPrimed = new HashMap <>();
                getActionVar(opApplNode, hmapUnprimed, hactionmapPrimed);
                Set set1 = hmapUnprimed.entrySet();
                Iterator iterator1 = set1.iterator();
                String reqStmt = "";
                while (iterator1.hasNext()) {
                    Map.Entry mentry;
                    mentry = (Map.Entry) iterator1.next();
                    var = (UniqueString) mentry.getKey();
                    val = (UniqueString) mentry.getValue();
                    reqStmt = reqStmt + " && " + var + "=" + capitalizeFirstL(val);
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
                    writer.write(capitalizeFirstL(updatevar) + ":=" + capitalizeFirstL(updateval) + ";");
                    writer.write("\n");
                }
                writer.write("}");
                //writer.write("{" + updatevar + ":=" + updateval + ";}");
                writer.write("\n");
                writer.write("\n");
            }



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
            UniqueString unPrimedVariable = UniqueString.uniqueStringOf(capitalizeFirstL(UniqueString.uniqueStringOf(unPrimedVar + "[" + unPrimedArg + "]")));
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
                    if (symbolNode.getArity() == 0) {
                        //hmapUnprimed.put(opName, String.valueOf(getStringVal(conj.getArgs()[1])));
                        hmapUnprimed.put(UniqueString.uniqueStringOf(capitalizeFirstL(opName)), getVar(conj.getArgs()[1]));

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
                                for(int j=0;j<primedArgs.length;j++){
                                    if (getVar(primedArgs[j]).equals("$Pair")) {
                                        OpApplNode opApplNode2 = (OpApplNode)primedArgs[j];
                                        ExprOrOpArgNode[] exprOrOpArgNode = opApplNode2.getArgs(); //getting ![rm]="aborted" in exprOrOpArgNode[0]
                                        OpApplNode opApplNode3 = (OpApplNode) exprOrOpArgNode[0];
                                        ExprOrOpArgNode[] exprOrOpArgNode1 = opApplNode3.getArgs(); // get parameter in Except
                                        UniqueString primedVariable = UniqueString.uniqueStringOf(primedVar + "[" + getVar(exprOrOpArgNode1[0]).toString().toLowerCase() + "]");
                                        hactionmapPrimed.put(primedVariable, getVar(exprOrOpArgNode[1]));
                                    }

                                }
                            }
                        }

                    }
                    if (opName.equals("$FcnApply")) { //rmState[rm]


                        ExprOrOpArgNode[] argNode = opApplNode1.getArgs();
                        UniqueString unPrimedVar = getVar(argNode[0]);
                        UniqueString unPrimedArg = UniqueString.uniqueStringOf(getVar(argNode[1]).toString().toLowerCase());
                        UniqueString unPrimedVariable = UniqueString.uniqueStringOf(unPrimedVar + "[" + unPrimedArg + "]");
                        hmapUnprimed.put(UniqueString.uniqueStringOf(capitalizeFirstL(unPrimedVariable)), getVar(conj.getArgs()[1]));
                    }
                    if (opName.equals("\\in")) {                         //forall_other rm. (State[rm] = ProposeCommit)
                        ExprOrOpArgNode[] argNode = opApplNode1.getArgs();
                        OpApplNode opApplNode11 = (OpApplNode) argNode[0]; //(State[rm] = ProposeCommit)
                        ExprOrOpArgNode[] argNode1 = opApplNode11.getArgs();
                        OpApplNode opApplNode12 = (OpApplNode) argNode1[0]; //State
                        OpApplNode opApplNode13 = (OpApplNode) argNode1[1]; //rm
                        UniqueString primedVar = getVar(opApplNode12);
                        UniqueString primedVar1 = getVar(opApplNode13);
                        UniqueString unPrimedVariable = UniqueString.uniqueStringOf("forall_other " + primedVar1.toString().toLowerCase() + ".(" + capitalizeFirstL(primedVar) + "[" + primedVar1.toString().toLowerCase() + "]");
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
            String initStr1 = capitalizeFirstL(UniqueString.uniqueStringOf(String.valueOf(objKey))) + "=" + capitalizeFirstL(stringNode.getRep()) + " && ";
            return initStr1;
        }
        if (objVal instanceof OpApplNode) { // for function
            OpApplNode node1 = (OpApplNode) objVal; //get function
            UniqueString node2 = node1.getOperator().getName(); //$FcnConstructor
            if(node2.equals("$FcnConstructor")){
                ExprOrOpArgNode[] setFcns = node1.getArgs();
                ExprNode setf = (ExprNode) setFcns[0];
                StringNode stringNode = (StringNode) setf;// get value i.e "working"
                String initStr1 = capitalizeFirstL(UniqueString.uniqueStringOf(String.valueOf(objKey))) + "[" + initParam + "]=" + capitalizeFirstL(stringNode.getRep()) + " && ";
                return initStr1;
            }
            return null;

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

    private static String SetEnumerators(ExprOrOpArgNode[] exprOrOpArgNodes) throws  Exception {
        String varList = "";
        for (int i = 0; i < exprOrOpArgNodes.length; i++) {
            if (exprOrOpArgNodes[i] instanceof StringNode){
                StringNode expr1 = (StringNode) exprOrOpArgNodes[i];
                if (i == 0) {
                    // varList = varList.concat(String.valueOf(expr1.getRep()));
                    varList = varList.concat(String.valueOf(capitalizeFirstL(expr1.getRep())));


                } else {
                    varList = varList.concat(" | " + String.valueOf(capitalizeFirstL(expr1.getRep())));
                }
            }
            else{
                throw new  Exception("SetEnumerate is not in String format : "+exprOrOpArgNodes.getClass());
            }

        }
        return varList;
    }

    private static String capitalizeFirstL(UniqueString rep) {
        if (rep != null) {
            String output = rep.toString().substring(0, 1).toUpperCase() + rep.toString().substring(1);
            return output;

        }
        return null;
    }

    private static String lowerFirstL(UniqueString rep) {
        if (rep != null) {
            String output = rep.toString().substring(0, 1).toLowerCase() + rep.toString().substring(1);
            return output;

        }
        return null;
    }
}