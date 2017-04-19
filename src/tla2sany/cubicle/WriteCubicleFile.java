// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS WriteCubicleFile                                                       *
*                                                                          *
* Contains the method Write for writing out a tokenized spec as a TLA      *
* file, deleting the "`^ ... ^'" parts of comments, and replacing "`~",    *
* "~'", "`.", and ".'" by spaces.                                          *
***************************************************************************/
package tla2sany.cubicle ;
import tla2sany.semantic.OpDeclNode;
import util.UniqueString;

import java.io.*;
import java.lang.reflect.Array;
import java.util.Arrays;
import java.util.Vector;

public class WriteCubicleFile
 { public static void Write(String fileName, Vector<OpDeclNode> list, UniqueString[] varNames)
    {
	 try{
	 File file = new File(fileName);

     
     // creates the file
     file.createNewFile();
     
     // creates a FileWriter Object
     FileWriter writer = new FileWriter(file); 
     
     // Writes the variables to the file
    for (int i=0; i<varNames.length; i++) {
        String var1 = "var "+varNames[i]+":"+varNames[i]+"1";
        writer.write(var1);
        writer.write("\n");
    }

     writer.flush();
     writer.close();
	 }
	 catch (IOException e) {

			e.printStackTrace();
		 
	 }

    }
 }  