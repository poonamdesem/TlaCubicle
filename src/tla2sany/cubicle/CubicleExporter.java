
// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.cubicle;

/**
 * a tool for exporting the loaded modules to XML format
 */
import java.lang.reflect.Array;
import java.util.*;
import java.awt.List;
import java.awt.image.SampleModel;
import java.io.PrintStream;
import java.io.ByteArrayOutputStream;

import tla2sany.drivers.SANY;
import tla2sany.drivers.FrontEndException;
import tla2sany.configuration.Configuration;
import tla2sany.explorer.Explorer;
import tla2sany.explorer.ExplorerQuitException;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.*;
import tla2sany.st.Location;
import tla2sany.semantic.ModuleNode;
import tlc2.tool.BuiltInOPs;
import tlc2.util.Vect;
import tlc2.TLCGlobals;
import tlc2.value.IntValue;
import util.FileUtil;
import util.ToolIO;
import util.UniqueString;
import util.FilenameToStream;
import util.SimpleFilenameToStream;


// XML packages
import java.io.File;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Schema;
import javax.xml.validation.Validator;
import org.xml.sax.SAXException;
import java.net.URL;
import java.net.MalformedURLException;

import org.w3c.dom.Attr;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class CubicleExporter {

  public static final void main(String[] args) throws Exception  {

    // parse arguments, possible flag
    // s
    // -I (a modules path) can be repeated
    // then a list of top level modules to parse)
    if (args.length < 1) throw new IllegalArgumentException("at least one .tla file must be given");
    LinkedList pathsLs = new LinkedList();

    boolean offline_mode = false;
    int lastarg = -1; // lastarg will be incremented, initialize at -1
    for (int i = 0; i<args.length-1; i++) {
    	if ("-I".equals(args[i])) {
            i++;
            if (i > args.length-2) throw new IllegalArgumentException("the -I flag must be followed by a directory and at least one .tla file");
            pathsLs.addLast(args[i]);
            lastarg = i;
        }
    }

    lastarg++;

    String[] paths = new String[pathsLs.size()];
    for (int i=0; i<paths.length; i++) paths[i] = (String)pathsLs.get(i);

    String[] tlas = new String[args.length - lastarg];
    for (int i=0; i<args.length-lastarg; i++) tlas[i] = args[lastarg++];

    FilenameToStream fts = new SimpleFilenameToStream(paths);

    // redirecting System.out
    //PrintStream out = System.out;
    //System.setOut(new PrintStream(new ByteArrayOutputStream()));

    SpecObj[] specs = new SpecObj[tlas.length];
    for (int i=0; i<tlas.length; i++){ specs[i] = new SpecObj(tlas[i], fts);
    // For each file named on the command line (i.e. in the tlas
    // array) (re)initialize the entire system and process that file
    // as the root of a new specification.
    //for (int i = 0; i < tlas.length; i++) {
      // continue the loop where the last one left off
      // Print documentation line on System.out
      ToolIO.out.println("\n****** SANY2 " + SANY.version + "\n") ;

      // Get next file name from command line; then parse,
      // semantically analyze, and level check the spec started in
      // file Filename leaving the result (normally) in Specification
      // spec.
      // check if file exists
      if (FileUtil.createNamedInputStream(tlas[i], specs[i].getResolver()) != null)
      {
          try {
              SANY.frontEndMain(specs[i], tlas[i], System.err);
              if (specs[i].getExternalModuleTable() == null)
                throw new Exception("spec " + specs[i].getName() + " is malformed - does not have an external module table", null);
              if (specs[i].getExternalModuleTable().getRootModule() == null)
                throw new Exception("spec " + specs[i].getName() + " is malformed - does not have a root module", null);
            }
            catch (FrontEndException fe) {
              // For debugging
              fe.printStackTrace();
              ToolIO.out.println(fe);
              return;
            }
      } else
      {
          ToolIO.out.println("Cannot find the specified file " + tlas[i] + ".");
      }
    }
    
    // CALL TO CUBICLE CODE GOES HERE
    ModuleNode m = specs[0].getExternalModuleTable().getRootModule();
    int j = tlas[0].indexOf(".");
    String ext = tlas[0].substring(j + 1);
    String CubicleOutFile = tlas[0].replace(ext,"cub");
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
      for (int i = 0; i < varDecls.length; i++)
      {
          variablesNodes[i] = varDecls[i];
          varNames[i] = varDecls[i].getName();
          // varNames[i].setLoc(i);

      }
    OpDefNode[] arrOpt = m.getOpDefs();
    Vector<OpDeclNode> list = new Vector<OpDeclNode>();
    Vector<FormalParamNode> fps = new Vector<FormalParamNode>();
      //findDecls(node,list,fps);
      for (int i=0;i<arrOpt.length;i++){
          findDecls(arrOpt[i].getBody() ,list,fps);
         System.out.println(arrOpt[i].getName() + " == "+list+"Formal Parameter"+fps);

      }
      WriteCubicleFile.Write(CubicleOutFile,list,varNames);
      //System.out.println("list == "+list);

   // System.out.println("operator definition node"+Arrays.toString(arrOpt));



  }
  
  private static void findDecls(LevelNode node, Vector<OpDeclNode> list, Vector<FormalParamNode> fps) throws Exception {
      if (node == null) return;
	  if (node instanceof StringNode)
		  return;
	  if (node instanceof OpDeclNode) {
		  OpDeclNode opd = (OpDeclNode) node;
		  System.out.println("Found decl of OpDeclNode== "+opd.getName());
          list.add(opd);
		  return;
	  }
	  if (node instanceof OpDefNode) {
          OpDefNode opdef = (OpDefNode) node;
          System.out.println("Found decl of OpDefNode== " + opdef.getName());
          UniqueString opName = opdef.getName();
          int opcode = BuiltInOPs.getOpCode(opName);
          //System.out.print("OpCode==="+opcode+" ");
          /*switch (opcode) {
              case 7: // DisList
              {

                  System.out.println("Found decl of OpDefNode== " + opdef.getName() +"  OpCode= in Case=="+opcode);
                  //findDecls(opdef.getBody(),list,fps);

                  break;
              }
              case 6: // ConjList
              {
                  System.out.println("Found decl of OpDefNode== " + opdef.getName()+" OpCode= in Case=="+opcode);

                  break;
              }
              case 42: // \in
              {
                  System.out.println("Found decl of OpDefNode== " + opdef.getName()+"OpCode in Case=="+opcode);

                  break;
              }
              case 0: // Action
              {
                  System.out.println("Found decl of OpDefNode== " + opdef.getName()+"   OpCode in Case=="+opcode);

                  break;
              }

              default:
              {
                  return;
              }

          }
          */
          findDecls(opdef.getBody(),list,fps);
          return;
      }
	 /* if(node instanceof DecimalNode){
          OpDeclNode decNode = (OpDeclNode) node;
          list.add(decNode);
          return;
      }*/
      if(node instanceof NumeralNode){
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
          findDecls(OpNode, list,fps);
          for (int i = 0; i < args.length; i++) {
               findDecls(args[i], list,fps);
          }
         return;
      }
      if (node instanceof FormalParamNode){
          FormalParamNode formalParamNode = (FormalParamNode) node;
          fps.add(formalParamNode);
         // System.out.println("Found decl of FormalParamNode=="+symbolNode.getName());
          fps.add(formalParamNode);
          return;
      }

      throw new Exception("Unhandled case: "+node.getClass());

  }

  }

