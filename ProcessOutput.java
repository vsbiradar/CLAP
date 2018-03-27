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
import java.util.*;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.io.*;

import org.jgrapht.graph.DefaultWeightedEdge;
import org.jgrapht.graph.DirectedWeightedMultigraph;

public class ProcessOutput {

	public static void main(String[] args) throws IOException {

		String project = args[0];
		String testcase = args[1];

		String inPath = "Testcases/" + project + "/output/" + testcase;
		String outPath = "Testcases/" + project + "/processed-output/"
				+ testcase;

		System.out.println("Processing " + testcase + " of " + project);

		// Read the contents of the output file into a string
		String in = new String(Files.readAllBytes(Paths.get(inPath)));

		/*
		 * // my code int i=0; int size=in.length(); System.out.println(in);
		 * System.out.println(size); int ballid[]=new int[size]; for(char
		 * c:in.toCharArray()) { ballid[i]=Integer.valueOf(c)-48;
		 * 
		 * i++; }
		 */
		/*
		 * 
		 * Write your algorithm which does the post-processing of the output
		 */
		PrintWriter out = new PrintWriter(outPath);
		
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
			    String[] words=line.split("&");
			    
			    String first3fields=words[0];
			    sb.append(first3fields);
		
			    int ithballid=1;
			    while(ithballid<words.length)
			    {
			    c=Integer.parseInt(words[ithballid]);
			  
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

		return;
	}

}