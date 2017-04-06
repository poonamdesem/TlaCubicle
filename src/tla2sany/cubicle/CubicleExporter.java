
// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.cubicle;

/**
 * a tool for exporting the loaded modules to XML format
 */
import java.util.Arrays;
import java.awt.image.SampleModel;
import java.io.PrintStream;
import java.io.ByteArrayOutputStream;
import java.util.Iterator;
import java.util.LinkedList;

import tla2sany.drivers.SANY;
import tla2sany.drivers.FrontEndException;
import tla2sany.configuration.Configuration;
import tla2sany.explorer.Explorer;
import tla2sany.explorer.ExplorerQuitException;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.BuiltInLevel;
import tla2sany.semantic.Context;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.Generator;
import tla2sany.semantic.LabelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tla2sany.semantic.ModuleNode;
import util.FileUtil;
import util.ToolIO;
import util.UniqueString;
import util.FilenameToStream;
import util.SimpleFilenameToStream;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.InstanceNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;


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
    if (CubicleOutFile!= "")
    {
        WriteCubicleFile.Write(CubicleOutFile);
        System.out.println("Wrote -CubicleOut file " + CubicleOutFile);
    }
    
    // main entry data structure is specs[i].getExternalModuleTable().getRootModule()
    if (specs.length != 1) throw new Exception("We only handle one argument.");
    System.out.println("The root module name is:" + m.getName());
       
    
   // CubicleTranslation.Translate(LabelNode Node);
    SampleVisitor.main(args);
   
   /* void translate(LevelNode node) {
        if (node instanceof OpDeclNode) {
       	 OpDecl n = (OpDeclNode) node;
       	 System.out.println(node.getName());
       	 return;
        }
    }*/
    
    
  }
    

     
  }

