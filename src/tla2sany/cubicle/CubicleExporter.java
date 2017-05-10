
// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.cubicle;

/**
 * a tool for exporting the loaded modules to XML format
 */

import java.util.*;

import tla2sany.drivers.SANY;
import tla2sany.drivers.FrontEndException;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.*;
import tla2sany.semantic.ModuleNode;
import tlc2.tool.BuiltInOPs;
import tlc2.value.IntValue;
import util.FileUtil;
import util.ToolIO;
import util.UniqueString;
import util.FilenameToStream;
import util.SimpleFilenameToStream;


// XML packages


public class CubicleExporter {

    public static final void main(String[] args) throws Exception {

        // parse arguments, possible flag
        // s
        // -I (a modules path) can be repeated
        // then a list of top level modules to parse)
        if (args.length < 1) throw new IllegalArgumentException("at least one .tla file must be given");
        LinkedList pathsLs = new LinkedList();

        boolean offline_mode = false;
        int lastarg = -1; // lastarg will be incremented, initialize at -1
        for (int i = 0; i < args.length - 1; i++) {
            if ("-I".equals(args[i])) {
                i++;
                if (i > args.length - 2)
                    throw new IllegalArgumentException("the -I flag must be followed by a directory and at least one .tla file");
                pathsLs.addLast(args[i]);
                lastarg = i;
            }
        }

        lastarg++;

        String[] paths = new String[pathsLs.size()];
        for (int i = 0; i < paths.length; i++) paths[i] = (String) pathsLs.get(i);

        String[] tlas = new String[args.length - lastarg];
        for (int i = 0; i < args.length - lastarg; i++) tlas[i] = args[lastarg++];

        FilenameToStream fts = new SimpleFilenameToStream(paths);

        // redirecting System.out
        //PrintStream out = System.out;
        //System.setOut(new PrintStream(new ByteArrayOutputStream()));

        SpecObj[] specs = new SpecObj[tlas.length];
        for (int i = 0; i < tlas.length; i++) {
            specs[i] = new SpecObj(tlas[i], fts);
            // For each file named on the command line (i.e. in the tlas
            // array) (re)initialize the entire system and process that file
            // as the root of a new specification.
            //for (int i = 0; i < tlas.length; i++) {
            // continue the loop where the last one left off
            // Print documentation line on System.out
            ToolIO.out.println("\n****** SANY2 " + SANY.version + "\n");

            // Get next file name from command line; then parse,
            // semantically analyze, and level check the spec started in
            // file Filename leaving the result (normally) in Specification
            // spec.
            // check if file exists
            if (FileUtil.createNamedInputStream(tlas[i], specs[i].getResolver()) != null) {
                try {
                    SANY.frontEndMain(specs[i], tlas[i], System.err);
                    if (specs[i].getExternalModuleTable() == null)
                        throw new Exception("spec " + specs[i].getName() + " is malformed - does not have an external module table", null);
                    if (specs[i].getExternalModuleTable().getRootModule() == null)
                        throw new Exception("spec " + specs[i].getName() + " is malformed - does not have a root module", null);
                } catch (FrontEndException fe) {
                    // For debugging
                    fe.printStackTrace();
                    ToolIO.out.println(fe);
                    return;
                }
            } else {
                ToolIO.out.println("Cannot find the specified file " + tlas[i] + ".");
            }
        }

        // CALL TO CUBICLE CODE GOES HERE
        ModuleNode m = specs[0].getExternalModuleTable().getRootModule();
        int j = tlas[0].indexOf(".");
        String ext = tlas[0].substring(j + 1);
        String CubicleOutFile = tlas[0].replace(ext, "cub");
    /*if (CubicleOutFile!= "")
    {
        WriteCubicleFile.Write(CubicleOutFile);
        System.out.println("Wrote -CubicleOut file " + CubicleOutFile);
    }   */
        // main entry data structure is specs[i].getExternalModuleTable().getRootModule()
        if (specs.length != 1) throw new Exception("We only handle one argument.");
        // Get all the state variables in the spec:
        OpDeclNode[] variablesNodes; // The state variables.
        OpDeclNode[] varDecls = m.getVariableDecls();
        variablesNodes = new OpDeclNode[varDecls.length];
        UniqueString[] varNames = new UniqueString[varDecls.length];
        for (int i = 0; i < varDecls.length; i++) {
            variablesNodes[i] = varDecls[i];
            varNames[i] = varDecls[i].getName();
        }
        OpDefNode[] arrOpt = m.getOpDefs();
        Vector <OpDeclNode> list = new Vector <OpDeclNode>();
        Vector <FormalParamNode> fps = new Vector <FormalParamNode>();
        HashMap <UniqueString, OpApplNode> hmap = new HashMap <>();
        HashMap <UniqueString, ExprNode> initHmap = new HashMap <>();
        HashMap <UniqueString, OpApplNode> hnext = new HashMap <>();
        LevelNode levelNode=null;

        Scanner scanner = new Scanner(System.in);
        System.out.println("Enetr Spec name to create unsafe state");
        String specInput = scanner.next();
        System.out.println("Input=="+specInput);


        for (int i = 0; i < arrOpt.length; i++) {
            if (arrOpt[i].getName().equals("TypeOK")) {
                findVariableDecls(arrOpt[i], hmap);
            }
            if (arrOpt[i].getName().equals("Init")) {
                findInitialization(arrOpt[i], initHmap);
            }
            if (arrOpt[i].getName().equals("Next")) {
                findNext(arrOpt[i], hnext);
            }
            if(arrOpt[i].getName().equals(specInput)){
                levelNode = arrOpt[i].getBody();
            }

            // findDecls(arrOpt[i].getBody(),list,fps);
            // findDecls(arrOpt[i].getBody(),arrOpt[i].getName(),list,fps);
            // System.out.println(arrOpt[i].getName());
        }
        WriteCubicleFile.Write(CubicleOutFile, hmap, initHmap,hnext,levelNode);
        /*String command= "/usr/bin/xterm";
        String command1= "cd /home/poonam/TCtest";
        Runtime rt = Runtime.getRuntime();
        Process pr = rt.exec(command);
        Process pr1 = rt.exec(command1);*/
    }

    /*
    findNext method iterate through outer disList of Next and return the hnext hashmap containing the action name in key
    and opAppNode(action name with parameter) in value.

     */

    private static void findNext(OpDefNode opDefNode, HashMap <UniqueString, OpApplNode> hnext) throws Exception {
        LevelNode node = opDefNode.getBody();
        String nextId = "";
        String nextParam = "";
        Boolean flag=true;
        if (node instanceof OpApplNode) {
            OpApplNode node1 = (OpApplNode) node;
            ExprOrOpArgNode[] disjList = node1.getArgs();
            for (int i = 0; i < disjList.length; i++) { // get outer disList in Next
                OpApplNode opApplNode = (OpApplNode) disjList[i];
                 hnext.put(opApplNode.getOperator().getName(), opApplNode);
                if (opApplNode.getOperator().getName().equals("\\lor")){
                    hnext.remove(opApplNode.getOperator().getName()); // "\\lor" from hashmap

                    ExprOrOpArgNode[] argNode = opApplNode.getArgs();
                    for (int j = 0; j < argNode.length; j++) {
                        if (argNode[j] instanceof OpApplNode) {
                            OpApplNode opApplNode1 = (OpApplNode) argNode[j];
                           // System.out.println("String2 == " + opApplNode1.getOperator().getName());
                             hnext.put(opApplNode1.getOperator().getName(), opApplNode1);
                        }
                    }
                }
                if (opApplNode.getOperator().getName().equals("$BoundedExists")) {
                    hnext.remove(opApplNode.getOperator().getName()); // remove $BoundedExists from hashmap
                    FormalParamNode[][] formalParamNodes = opApplNode.getBdedQuantSymbolLists(); //get existential parameter rm

                    for (int j = 0; j < formalParamNodes[0].length; j++) {
                        SymbolNode symbolNode = (SymbolNode) formalParamNodes[0][j];

                        nextId = nextId.concat(String.valueOf(symbolNode.getName()) + ",");
                    }
                    if (nextId != null) {
                        nextParam = nextId.substring(0, nextId.length() - 1);
                    }
                    ExprOrOpArgNode[] argNode1 = opApplNode.getArgs();
                    for (int k = 0; k < argNode1.length; k++) {
                        if (argNode1[k] instanceof OpApplNode) {
                            OpApplNode opApplNode2 = (OpApplNode) argNode1[k];
                            ExprOrOpArgNode[] exprOrOpArgNodes = opApplNode2.getArgs();
                            for (int l = 0; l < exprOrOpArgNodes.length; l++) {
                                OpApplNode opApplNode1 = (OpApplNode) exprOrOpArgNodes[l];
                                if(opApplNode1.getOperator().getName().equals("\\lor")){
                                    throw new  Exception("Next is not in required format");
                                }else{
                                    hnext.put(opApplNode1.getOperator().getName(), opApplNode1);
                                    //System.out.println("String3 == " + opApplNode1.getOperator().getName()+"=="+opApplNode1);


                                }
                            }
                        }
                    }

                }
                 /*   ExprNode[] exprNode1 = opApplNode.getBdedQuantBounds(); // getting RM in Next
                    FormalParamNode[][] formalParamNodes = opApplNode.getBdedQuantSymbolLists(); //get existential parameter rm
                    for (int j = 0; j < formalParamNodes[0].length; j++) {
                        SymbolNode symbolNode = (SymbolNode) formalParamNodes[0][j];
                        nextId = nextId.concat(String.valueOf(symbolNode.getName()) + ",");
                    }
                    if (nextId != null) {
                        nextParam = nextId.substring(0, nextId.length() - 1);
                    }*/

            }
            /*Set hset = hnext.entrySet();
            Iterator it = hset.iterator();
            while (it.hasNext()) {
                Map.Entry me = (Map.Entry) it.next();

                System.out.println("value=" + me.getValue()+" key=" + me.getKey());
            }*/

        }

    }

    private static void findInitialization(OpDefNode opDefNode, HashMap <UniqueString, ExprNode> initHmap) throws Exception {
        LevelNode node = opDefNode.getBody();
        if (node instanceof OpApplNode) {
            OpApplNode node1 = (OpApplNode) node;
            ExprOrOpArgNode[] conjList = node1.getArgs();
            for (int i = 0; i < conjList.length; i++) {
                ExprNode conj = (ExprNode) conjList[i];
                OpApplNode opApplNode = (OpApplNode) conj;
                ExprOrOpArgNode[] argNode = opApplNode.getArgs();
                OpApplNode opApplNode1 = (OpApplNode) argNode[0];
                //System.out.print(argNode[1]); // till here same as findVariableDecls method, can be put into switch case of single method
                if (argNode[1] instanceof ExprNode) {
                    ExprNode exprNode = (ExprNode) argNode[1];
                    initHmap.put(opApplNode1.getOperator().getName(), exprNode);
                } else {
                    throw new Exception("Unhandled case: " + argNode[1].getClass());
                }
            }
        }

    }

    private static void findVariableDecls(OpDefNode opDefNode, HashMap <UniqueString, OpApplNode> hmap) throws Exception {
        if (opDefNode.getName().equals("TypeOK")) {
            LevelNode node = opDefNode.getBody();
            if (node instanceof OpApplNode) {
                OpApplNode node1 = (OpApplNode) node;
                ExprOrOpArgNode[] conjList = node1.getArgs();// get set of conjunction in TypeOK
                for (int i = 0; i < conjList.length; i++) {
                    ExprNode conj = (ExprNode) conjList[i];
                    OpApplNode opApplNode = (OpApplNode) conj;
                    ExprOrOpArgNode[] argNode = opApplNode.getArgs();
                    SymbolNode OpNode = opApplNode.getOperator(); // \in operator
                    int opcode = BuiltInOPs.getOpCode(OpNode.getName());

                    UniqueString opName = OpNode.getName();
                    if (argNode.length == 2) {
                        OpApplNode opApplNode1 = (OpApplNode) argNode[0];
                        OpApplNode opApplNode2 = (OpApplNode) argNode[1];
                        hmap.put(opApplNode1.getOperator().getName(), opApplNode2);
                    }
                    Set set = hmap.entrySet();
                    Iterator iterator = set.iterator();
                    while (iterator.hasNext()) {
                        Map.Entry mentry = (Map.Entry) iterator.next();
                        // System.out.print("key is: "+ mentry.getKey() + " & Value is: ");
                        // System.out.println(mentry.getValue());
                    }

                }

            } else {
                throw new Exception("Unhandled case: " + node.getClass());
            }

        }
    }

    private static void findDecls(LevelNode node, UniqueString name, Vector <OpDeclNode> list, Vector <FormalParamNode> fps) throws Exception {
        if (node == null) return;
        if (node instanceof StringNode)
            return;
        if (node instanceof OpDeclNode) {
            OpDeclNode opd = (OpDeclNode) node;
            System.out.println("Found decl of OpDeclNode== " + opd.getName());
            list.add(opd);
            return;
        }
        if (node instanceof OpDefNode) {
            OpDefNode opdef = (OpDefNode) node;
            System.out.println("Found decl of OpDefNode== " + opdef.getName());
            UniqueString opName = opdef.getName();
            findDecls(opdef.getBody(), name, list, fps);
            return;
        }
        if (node instanceof NumeralNode) {
            NumeralNode numNode = (NumeralNode) node;
            IntValue val = IntValue.gen(numNode.val());
            //list.add(val);
            return;
        }
        if (node instanceof OpApplNode) {
            OpApplNode node1 = (OpApplNode) node;
            ExprOrOpArgNode[] args = node1.getArgs();
            SymbolNode OpNode = node1.getOperator();
            UniqueString opName = OpNode.getName();

        /* if(opDefNode.getName().equals("TypeOK")){
             LevelNode node = opDefNode.getBody();
             OpApplNode node1 = (OpApplNode) node;
             ExprOrOpArgNode[] args = node1.getArgs();// get set of conjunction in TypeOK
             for (int i = 0;i<args.length;i++){
                 ExprNode conj = (ExprNode) args[i];
                 findDecls(conj, list,fps);

             }
         }*/
            if (OpNode instanceof OpDefNode) {
                OpDefNode opDefNode = (OpDefNode) OpNode;
                int opcode = BuiltInOPs.getOpCode(opDefNode.getName());
                boolean isSetEnum = (opDefNode.getName().equals("$SetEnumerate"));
                boolean isCL = (opDefNode.getName().equals("$CongList"));
                if (isSetEnum) {
                    ExprOrOpArgNode[] exprOrOpArgNodes = node1.getArgs();
                    HashMap <UniqueString, UniqueString> hmap = new HashMap <>();
                    for (int i = 0; i < exprOrOpArgNodes.length; i++) {
                        StringNode expr1 = (StringNode) exprOrOpArgNodes[i];
                        // hmap.put(opd.getName(),expr1.getRep());
                        System.out.print("String == " + expr1.getRep());
                    }

                }
                if (name.equals("TypeOK")) {
                    if (isCL) {
                        ExprOrOpArgNode[] args1 = node1.getArgs();// get set of conjunction in TypeOK
                        for (int i = 0; i < args.length; i++) {
                            ExprNode conj = (ExprNode) args[i];
                            findDecls(conj, name, list, fps);
                        }
                    }
                }
            }
            findDecls(OpNode, name, list, fps);
            for (int i = 0; i < args.length; i++) {
                findDecls(args[i], name, list, fps);
            }
            return;
        }
        if (node instanceof FormalParamNode) {
            FormalParamNode formalParamNode = (FormalParamNode) node;
            fps.add(formalParamNode);
            // System.out.println("Found decl of FormalParamNode=="+symbolNode.getName());
            fps.add(formalParamNode);
            return;
        }

        throw new Exception("Unhandled case: " + node.getClass());

    }
}

//http://beginnersbook.com/2013/12/hashmap-in-java-with-example/