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

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Scanner;
import java.util.Set;

import org.jgrapht.graph.DefaultWeightedEdge;
import org.jgrapht.graph.DirectedWeightedMultigraph;

import soot.PackManager;
import soot.Transform;
import soot.toolkits.graph.ExceptionalBlockGraph;

public class TraceMaker {

	public static void main(String[] args) throws IOException {

		String project = args[0];
		String testcase = args[1];

		// Input args that were given to the testcase executable. 
		// These may be need during symbolic execution
		String argsFile = "Testcases/" + project + "/input/" + testcase;
		String testcaseArgs = new String(Files.readAllBytes(Paths.get(argsFile)));

        // The raw output from instrumented code. You'll use this to construct the tuple for each method call
		String inPath = "Testcases/" + project + "/output/" + testcase;

        // The output files for global trace and tuples. You'll output the results to these files
	//	String globalTraceOutPath = "Testcases/" + project + "/processed-output/" + testcase + ".global_trace";
		String tupleOutPath = "Testcases/" + project + "/processed-output/" + testcase + ".tuples";

		System.out.println("Processing " + testcase + " of " + project);

		// Read the contents of the output file into a string
		String in = new String(Files.readAllBytes(Paths.get(inPath)));

		/*
		 * 
		 * Write your algorithm which does the post-processing of the output
		 * to construct the tuple for each method call
		 * 
		 */
PrintWriter out = new PrintWriter(tupleOutPath);
		
		StringBuilder sb = new StringBuilder();

		// project -3
		
		HashMap<String, Integer> map2=new HashMap<>();
		int numberofcalls=0;
		
		//
		String str = "mapping.txt";
		String path=null;
		FileInputStream f = new FileInputStream(str);
		ObjectInputStream oinput = new ObjectInputStream(f);
        StringBuffer previouspath=new StringBuffer();
        // to handle with number of calls
        HashMap<String,Integer> numberofcallsmap=new HashMap<>();
        Scanner sc1=new Scanner(in);
        while(sc1.hasNext())
        {
        	String fieldline=sc1.nextLine();
        	String[] fields1=fieldline.split(",");
        	String keytomap=fields1[0]+fields1[1];
        	if(numberofcallsmap.containsKey(keytomap))
        	{
        		int max=numberofcallsmap.get(keytomap);
        		if(max<Integer.parseInt(fields1[2]))
        		{
        			numberofcallsmap.put(keytomap, Integer.parseInt(fields1[2]));
        		}
        	}
        	else
        		numberofcallsmap.put(keytomap, Integer.parseInt(fields1[2]));
        	
        }
		// System.out.println(in);
		int i = 0;
		int size = in.length();
		int max = 0, ballid;
		try {
			HashMap<Integer, String> hash = (HashMap<Integer, String>) oinput.readObject();
			
			Scanner sc=new Scanner(in);//.useDelimiter("\\n");
			int c;
			int j=0;
			
		
			while(sc.hasNext()) {

				
				//------ project-3------------------start
			    String line=sc.nextLine();	
			    String[] words=line.split(",");
			    System.out.println(line);
			    String first3fields=null;
			    if(numberofcallsmap.get(words[0]+words[1])==Integer.parseInt(words[2]))
			    {
			        first3fields=words[0]+","+words[1]+","+0+",";
			    }
			    else
			    {
			     first3fields=words[0]+","+words[1]+","+words[2]+",";	
			    }
			    if(Integer.parseInt(words[2])==0)
			    {
			    	first3fields=words[0]+","+words[1]+","+numberofcallsmap.get(words[0]+words[1])+",";
			    }
			    sb.append(first3fields);
			    
			    String ballids=words[3];
			    String realballids[]=ballids.split("&");
			    int ithballid=1;
			    
			    while(ithballid<realballids.length)
			    {
			    c=Integer.parseInt(realballids[ithballid]);
			  
			    //------project-3-------------------end
			
				max=0;
				ballid=c;
				Set<Integer> keys = hash.keySet();
				for (Integer key : keys) {
					//System.out.println(key);
					if (key <= ballid && key >= max) {
						max = key;
					}
				}

			//	System.out.println(keys);
				path = hash.get(max);
				if(j==0)
				{
					previouspath= new StringBuffer(path);
					j++;
				}	
			//	System.out.println(path);
				ballid = ballid - max;
				//System.out.println(ballid);
				FileInputStream f2 = new FileInputStream(path);
				ObjectInputStream outgraph = new ObjectInputStream(f2);
		
				DirectedWeightedMultigraph<Integer, DefaultWeightedEdge> g = (DirectedWeightedMultigraph<Integer, DefaultWeightedEdge>) outgraph.readObject();

			
				int x = -1, max2 = 0, weight, nextnode = 0;
				while (x != (-2)) 
				{
					max2 = 0;
					// List<DefaultWeightedEdge> l=(List<DefaultWeightedEdge>)
					// g.outgoingEdgesOf(x);
					for (DefaultWeightedEdge ed : g.outgoingEdgesOf(x)) 
					{
						weight = (int) g.getEdgeWeight(ed);
					   //  System.out.println(ed);
					    // System.out.println(weight);
						if (weight <= ballid && weight >= max2) 
						{
							// System.out.println(weight);
							max2 = weight;
							nextnode = g.getEdgeTarget(ed);
						}
					}
					ballid = ballid - max2;
					x = nextnode;
					if (nextnode != -2)
					{
						sb.append(x);
						sb.append("->");
					
					}
			
				}
				ithballid++;
			    }
			sb.append("\n");	
			}
		//	sb.deleteCharAt(0);
			
			sb.deleteCharAt(sb.length()-1);
	
			out.print(sb);
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		// out.print(in);

		out.close();

	//	return;

		//---------------------end of my code----------------------
		
		// Call to the symbolic execution.
		// You can pass any data that's required for symbolic execution
		// Example: the tuples for each method call
		
		/*
		String tuplesFile = "Testcases/" + project + "/processed-output/" + testcase + "-tuples";
		String tuples = new String(Files.readAllBytes(Paths.get(tuplesFile)));
		
		HashMap<String , String> hs31=new HashMap<>();
		Scanner sc1=new Scanner(tuples);
		while(sc1.hasNext())
		{
			String onetuple=sc1.nextLine();
			String[] tupleelement=onetuple.split(",");
			if(!tupleelement[1].equals("null"))
			{
				String fileforthread="file-"+tupleelement;     // file name for thread 
				if(!hs31.containsKey(tupleelement[1]))       // if file is not created then create one
				{
					FileOutputStream foutput=new FileOutputStream(fileforthread);
					hs31.put(tupleelement[1], "yes");
				}
				else       // if file created for same thread by some earlier tuple then open that file
				{
					FileInputStream foutput=new FileInputStream(fileforthread);
				}
				FileInputStream bgofmethod = new FileInputStream(tupleelement[0]+"exceptionalBG");  // get exceptional block graph for this method
				ObjectInputStream blockgraph = new ObjectInputStream(bgofmethod);
				try {
					ExceptionalBlockGraph cfg = (ExceptionalBlockGraph) blockgraph.readObject();   // read the blockgraph of that method
					Scanner sc31=new Scanner(tupleelement[3]).useDelimiter("->");
						while(sc31.hasNext())
							{
							int blockid=sc31.nextInt();
							// print the tarce while traversing the whole function
							}
				} catch (ClassNotFoundException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		
		
		
		*/
		
		sootMainSymbolicExecution(project, testcase);

        /*
            You should have the intra-thread trace for each thread and the
            path constraints by now.
            Assign an order variable of the form O_i_j to the jth trace entry
            of the ith thread.
            Use the intra-thread traces to construct read-write constraints,
            locking constraints, program order constraints, must-happen-before
            constraints. These constraints will be in terms of the order 
            variables.
            Put all these constaints together into one big equation:
            All_constraints = (Read-write constraints) ^ (Path constraints) ^
                (Program order constraints) ^ (Must happen before constraints)
                ^ (Locking constraints)
            
        */
        
        /* Solve the constraints using Z3 solver
           The solver will provide you a feasible assignment of order variables
           Using these values, construct your global trace 
           To construct the global trace, you just need to put the intra-thread
           trace entries in ascending order of their order variables.
        */

		// Output the global trace 
	//	PrintWriter globalTraceWriter = new PrintWriter(globalTraceOutPath);
	//	globalTraceWriter.println();

	//	globalTraceWriter.close();

		// Output the tuples
	//	PrintWriter tupleWriter = new PrintWriter(tupleOutPath);
	//	tupleWriter.println();

	//	tupleWriter.close();

		return;
	}

	public static void sootMainSymbolicExecution(String project, String testcase) {

		ArrayList<String> base_args = new ArrayList<String>();

		// This is done so that SOOT can find java.lang.Object
		base_args.add("-prepend-classpath");

		base_args.add("-w");

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
		base_args.add("-soot-class-path");
		base_args.add("Testcases/" + project + "/" + project + ".jar");

		// The Main class for the application
		base_args.add("-main-class");
		base_args.add(testcase + ".Main");

		// Class to analyze
		base_args.add(testcase + ".Main");

		base_args.add("-output-dir");
		base_args.add("Testcases/" + project + "/sootBin/");

		SymbolicExecution obj = new SymbolicExecution(project,testcase);

		PackManager.v().getPack("wjtp").add(new Transform("wjtp.MyAnalysis", obj));

		soot.Main.main(base_args.toArray(new String[base_args.size()]));

	}

}
