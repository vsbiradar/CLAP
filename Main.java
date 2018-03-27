package e0210;

/*
 * @author Sridhar Gopinath		-		g.sridhar53@gmail.com
 * 
 * Course project,
 * Principles of Programming Course, Fall - 2016,
 * Computer Science and Automation (CSA),
 * Indian Institute of Science (IISc),
 * Bangalore
 */

import java.util.ArrayList;

import soot.PackManager;
import soot.Transform;

//--------- my-code starts---------------
import java.util.ArrayList;
import soot.*;
import soot.Scene;
import soot.SootClass;
import soot.PackManager;
import soot.Transform;
import soot.options.Options;
//------------ends-----------------------
public class Main {

	public static void main(String[] args) {

		String project = args[0];
		String testcase = args[1];

		ArrayList<String> base_args = new ArrayList<String>();

		// This is done so that SOOT can find java.lang.Object
		base_args.add("-prepend-classpath");
		
		//base_args.add("-w");

		// Consider the Main Class as an application and not as a library
		base_args.add("-app");

		// Validate the Jimple IR at the end of the analysis
		base_args.add("-validate");

		// Exclude these classes and do not construct call graph for them
		base_args.add("-exclude");
		base_args.add("jdk.net");
		base_args.add("-exclude");
		base_args.add("java.lang");
		base_args.add("-exclude");
        base_args.add("jdk.internal.*"); 
		base_args.add("-no-bodies-for-excluded");

		// Retain variable names from the bytecode
		base_args.add("-p");
		base_args.add("jb");
		base_args.add("use-original-names:true");

		// Output the file as .class (Java Bytecode)
		base_args.add("-f");
		base_args.add("class");

		// Add the class path i.e. path to the JAR file
	//commented by me----:	base_args.add("-soot-class-path");
	//commented by me----:	base_args.add("Testcases/" + project + "/" + project + ".jar");

		configure("Testcases/"+project+"/"+project+".jar:bin/");
		
		// The Main class for the application
		base_args.add("-main-class");
		base_args.add(testcase + ".Main");

		// Class to analyze
		base_args.add(testcase + ".Main");

		base_args.add("-output-dir");
		base_args.add("Testcases/" + project + "/sootBin/");

		Analysis obj = new Analysis();
//-------------added by me------------
		Scene.v().addBasicClass("java.io.PrintStream",SootClass.SIGNATURES);
		Scene.v().addBasicClass("java.lang.System",SootClass.SIGNATURES);
//-----------ends-----------------------		

		PackManager.v().getPack("jtp").add(new Transform("jtp.MyAnalysis", obj));

		soot.Main.main(base_args.toArray(new String[base_args.size()]));
		obj.CreateFile();
		obj.finish(testcase);
		
		return;
	}
	public static void configure(String classpath) {
		// TODO Auto-generated method stub
		Options.v().set_verbose(false);
		Options.v().set_keep_line_number(true);
		Options.v().set_src_prec(Options.src_prec_class);
		Options.v().set_soot_classpath(classpath);
		Options.v().set_prepend_classpath(true);
	}

}
