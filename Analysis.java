package e0210;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;

/*
 * @author Sridhar Gopinath		-		g.sridhar53@gmail.com
 * 
 * Course project,
 * Principles of Programming Course, Fall - 2016,
 * Computer Science and Automation (CSA),
 * Indian Institute of Science (IISc),
 * Bangalore
 */

import java.util.Map;

import org.jgrapht.ext.DOTExporter;
import org.jgrapht.ext.VertexNameProvider;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedPseudograph;

import soot.Body;
import soot.BodyTransformer;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ExceptionalBlockGraph;


import java.util.*;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.OutputStream;

import soot.*;
import soot.jimple.*;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BlockGraph;
import soot.toolkits.graph.ExceptionalBlockGraph;
import soot.util.*;

import java.net.*;
import java.io.*;
import java.util.*;

import org.jgrapht.*;
import org.jgrapht.graph.DefaultWeightedEdge;
import org.jgrapht.graph.DirectedWeightedMultigraph;
import org.jgrapht.traverse.TopologicalOrderIterator;

public class Analysis extends BodyTransformer implements Serializable {
static SootMethod addtomap,addtomain,print2,concat;
	static SootClass helperClass;
	
	static {
		  helperClass = Scene.v().loadClassAndSupport("MyClass");
		  addtomap = helperClass.getMethod("void add(long)");
		  addtomain = helperClass.getMethod("void add2(java.lang.String)");
		  print2 = helperClass.getMethod("void print22(java.lang.String,int,java.lang.String)");
		  concat = helperClass.getMethod("java.lang.String concatinate(java.lang.String,int)");
	      
	}
	static HashMap<Integer,String> map=new HashMap<>();
	protected void CreateFile()
	{
		String str="mapping.txt";
		
		try {
			OutputStream f=new FileOutputStream(str);
			ObjectOutputStream out=new ObjectOutputStream(f);
			out.writeObject(map);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	  static int 	methodoffset;
	 private boolean addedclinit=false;
    private boolean addedOffset=false;
    private SootClass javaIoPrintStream;
	
	DirectedPseudograph<Block, DefaultEdge> graph = new DirectedPseudograph<Block, DefaultEdge>(DefaultEdge.class);




	@Override
	protected synchronized void internalTransform(Body b, String phaseName, Map<String, String> options) {

		ExceptionalBlockGraph cfg = new ExceptionalBlockGraph(b);
   // --------------------my-code starts-------------------------------------------------------------------------
	  SootMethod meth=b.getMethod();
   	  if(meth.getSignature().equals("<MyClass: void <clinit>()>")){
  		  return;
  	  }
  	  if(meth.getSignature().equals("<MyClass: void <init>()>")){
  		  return;
  	  }
  	  if(meth.getSignature().endsWith("void add(long)>")){
		  return;
	  }
   	  if(meth.getSignature().endsWith("void add2(java.lang.String)>"))
  	  {
  		  return;
  	  }
  	 if(meth.getSignature().endsWith("void print22(java.lang.String,int,java.lang.String)>"))
	  {
		  return;
	  }
  	 if(meth.getSignature().endsWith("java.lang.String concatinate(java.lang.String,int)>"))
  	 {
  		 return;
  	 }
     if(meth.getSignature().endsWith("void randomDelay()>"))
     {
    	 return;
     }
     if(meth.getSignature().endsWith("void randomDelay(int)>"))
    		 {
    	 return;
    		 }
     if(meth.getSignature().endsWith("init()>"))
	 {
          return;
	 }
     if(meth.getSignature().startsWith("<popUtil.PoP_Util"))
	 {
          return;
	 }

	 ExceptionalBlockGraph e=new ExceptionalBlockGraph(b);
	 System.out.println(e);
        List <Block> list = e.getBlocks();
        Iterator<Block> it=e.getBlocks().iterator();
        int n=list.size();
        int NumVertices;
        Local tmpRef=null,tmpRef1=null;
        int array[]=new int[100];
        int jnumpaths[]=new int[100];
        boolean addeddummy=false;
        Local ballid = Jimple.v().newLocal("ballid", IntType.v());
        b.getLocals().add(ballid);
        Local tmp=Jimple.v().newLocal("tmp", IntType.v());
        b.getLocals().add(tmp);
        Local tmp2=Jimple.v().newLocal("tmp2", IntType.v());
        b.getLocals().add(tmp2);
        Local tmp3=Jimple.v().newLocal("tmp3", IntType.v());
        b.getLocals().add(tmp3);
        Local childthreadid=Jimple.v().newLocal("childthreadid", LongType.v());
        Local parentthreadid=Jimple.v().newLocal("parentthreadid", LongType.v());
        b.getLocals().add(childthreadid);
        b.getLocals().add(parentthreadid);
        
        Local threadprint=Jimple.v().newLocal("threadprint", LongType.v());
        b.getLocals().add(threadprint);
        
        Local str32=Jimple.v().newLocal("str32", RefType.v("java.lang.String"));
        b.getLocals().add(str32);
        
        Local str33=Jimple.v().newLocal("str33", RefType.v("java.lang.String"));
        b.getLocals().add(str33);
        //  Local thread=Jimple.v().newLocal("tmp2", IntType.v());
        boolean isMain = b.getMethod().getSignature().equals("void main(java.lang.String[])");
        Chain units=b.getUnits();
       // PatchingChain ch1=new PatchingChain(units);
        int numpaths[]=new int[n];
	
        

        
	DirectedWeightedMultigraph<Integer,DefaultWeightedEdge > g=new DirectedWeightedMultigraph<Integer, DefaultWeightedEdge>(DefaultWeightedEdge.class);
        for(Block b2:list)
        {
        	g.addVertex(b2.getIndexInMethod());
        }
        g.addVertex(-1);
        g.addVertex(-2);
		for(Block b3:e.getTails()) // add edges from tails to end
		{
			g.addEdge(b3.getIndexInMethod(), -2);
		}
    	g.addEdge(-1, 0); 	
	     
		for(Block b2:list)
        {
        	List<Block> succ=b2.getSuccs();
        	for(Block bsucc:succ)
        	{
        		if(bsucc.getIndexInMethod()<=b2.getIndexInMethod())
        		{
        			
        			g.addEdge(-1, bsucc.getIndexInMethod());
        			g.addEdge(b2.getIndexInMethod(), -2);
        		}
        		else
        		g.addEdge(b2.getIndexInMethod(), bsucc.getIndexInMethod());
        	}
        }
//	 System.out.println(g);
        TopologicalOrderIterator<Integer,DefaultWeightedEdge> tpgraph=new TopologicalOrderIterator<Integer, DefaultWeightedEdge>(g);
        NumVertices=0;
        while(tpgraph.hasNext())
        {
        	array[NumVertices]=tpgraph.next();
        	NumVertices++;
        }
        int tail;
        jnumpaths[NumVertices-2]=1; // number of paths from tails to tail is one
        for(int i=NumVertices-3;i>=0;i--)
        {
        	jnumpaths[i]=0;
        	for(DefaultWeightedEdge m2:g.outgoingEdgesOf(i))
        	{
        		g.setEdgeWeight(m2, jnumpaths[i]);
        		if(g.getEdgeTarget(m2)==-2)
        			jnumpaths[i]=jnumpaths[i]+jnumpaths[NumVertices-2];
        		else
        		    jnumpaths[i]=jnumpaths[i]+jnumpaths[g.getEdgeTarget(m2)];
        	}
        }
      
	    int num=0,target2;
        for(DefaultWeightedEdge ed3:g.outgoingEdgesOf(-1))
        {
        	g.setEdgeWeight(ed3, num);
        	target2=jnumpaths[g.getEdgeTarget(ed3)];
        	num=num+target2;
        }
        // here ends applying ball larus to jgraph
  //      System.out.println(g);
        
        int totalpaths=num;
        // apply ball larus to Exceptional block graph e
      
        String str7=null;
        boolean addedmain=false;

	         //  String str="Testcase/project-2/mapping.txt";
        int offset=methodoffset;
  	    Iterator stmtIt = units.snapshotIterator();
  	    Stmt stmt41=null;
  	    while(stmtIt.hasNext())
  	    {
  	    	
  	    	Stmt stmt=(Stmt) stmtIt.next();
  	    	
  	    	if(!(stmt instanceof IdentityStmt))
  	    	{
  	    	
  	    		str7=b.getMethod().getSignature();
  	    	    map.put(methodoffset, str7);
  	    	    methodoffset=methodoffset+totalpaths;
  	 
  	    	   if(stmt41!=null)
  	    	   {
	    	      if(b.getMethod().getSignature().contains("clinit") && !(addedclinit) )
	    	      {
		        	InvokeExpr addexpr=Jimple.v().newStaticInvokeExpr(addtomain.makeRef(),StringConstant.v("dsada"));
		  
		        	units.insertAfter(Jimple.v().newInvokeStmt(addexpr), stmt41);
		        	addedclinit=true;
	    	      }
  	    	       if(isMain)
  	    	       {
  	    	    	if(!addedmain)
  	    	    	{
				
  	    	    		InvokeExpr addexpr=Jimple.v().newStaticInvokeExpr(addtomain.makeRef(),StringConstant.v("dsada"));
  	    	    		units.insertAfter(Jimple.v().newInvokeStmt(addexpr), stmt41);
  	    	    		addedmain=true;
  	    	    	}
  	    	       }
  	    	     units.insertAfter(Jimple.v().newAssignStmt(str33,StringConstant.v("")), stmt41);    	  
  	    		 units.insertAfter(Jimple.v().newAssignStmt(ballid,IntConstant.v(0)),stmt41);
  	    	   // units.insertBefore(Jimple.v().newAssignStmt(ballid,Jimple.v().newStaticFieldRef(methodoffsetballid.makeRef())),stmt);
  	    	    break;
  	    	    }
  	    	   else
  	    	   {
  	    		 if(b.getMethod().getSignature().contains("clinit") && !(addedclinit) )
	    	      {
		        	InvokeExpr addexpr=Jimple.v().newStaticInvokeExpr(addtomain.makeRef(),StringConstant.v("dsada"));
		  
		        	units.insertBefore(Jimple.v().newInvokeStmt(addexpr), stmt);
		        	addedclinit=true;
	    	      }
 	    	    if(isMain)
 	    	    {
 	    	    	if(!addedmain)
 	    	    	{
				
 	    	    		InvokeExpr addexpr=Jimple.v().newStaticInvokeExpr(addtomain.makeRef(),StringConstant.v("dsada"));
 	    	    		units.insertBefore(Jimple.v().newInvokeStmt(addexpr), stmt);
 	    	    		addedmain=true;
 	    	    	}
 	    	    }
 	    	    units.insertBefore(Jimple.v().newAssignStmt(str33,StringConstant.v("")), stmt);    	  
 	    		 units.insertBefore(Jimple.v().newAssignStmt(ballid,IntConstant.v(0)),stmt);
 	    	   // units.insertBefore(Jimple.v().newAssignStmt(ballid,Jimple.v().newStaticFieldRef(methodoffsetballid.makeRef())),stmt);
 	    	    break;
 	    		   
  	    	   }
  	    	}
  	    	stmt41=stmt;
  	    }
       
        for(Block bl:e.getBlocks())
        {
        	List<Block> succ=bl.getSuccs();
        	for(Block bsucc:succ)
        	{
           		if(bsucc.getIndexInMethod()<=bl.getIndexInMethod())
        		{
        		//	System.out.println("---- yeah yu arre ini looop----- handle it");
        	    DefaultWeightedEdge edge1=g.getEdge(bl.getIndexInMethod(), -2);  // edge going to end
                DefaultWeightedEdge edge2=g.getEdge(-1, bsucc.getIndexInMethod()); // edge coming from start         		   
                  	   // add edge weight of edge going to end to ballid
                AssignStmt st0=Jimple.v().newAssignStmt(ballid, Jimple.v().newAddExpr(ballid, IntConstant.v((int) g.getEdgeWeight(edge1))));
                units.insertOnEdge(st0, bl.getTail(), bsucc.getHead());
            		   
            		   // print the ballid
                AssignStmt st9=Jimple.v().newAssignStmt(ballid, Jimple.v().newAddExpr(ballid, IntConstant.v(offset)));
                units.insertAfter(st9, st0);
           
            	InvokeExpr concatExpr= Jimple.v().newStaticInvokeExpr(concat.makeRef(),str33,ballid);
 			    Stmt stmt13=Jimple.v().newAssignStmt(str33,concatExpr);
            	units.insertAfter(stmt13, st9);
  
                 
                 // Assign Ballid to the weight of edge coming from start
                AssignStmt st3=Jimple.v().newAssignStmt(ballid, IntConstant.v((int )g.getEdgeWeight(edge2)));
                 units.insertAfter(st3, stmt13);
            		//AssignStmt st2=Jimple.v().newAssignStmt(ballid, IntConstant.v((int)g.getEdgeWeight(edge2)));
            		//units.insertAfter(st2, st0);
            		//units.insertAfter(toInsert, st0);
            	continue;   
        		}
        		else
        		{
        			DefaultWeightedEdge edge3=g.getEdge(bl.getIndexInMethod(), bsucc.getIndexInMethod());
        			AssignStmt st1=Jimple.v().newAssignStmt(ballid, Jimple.v().newAddExpr(ballid, IntConstant.v((int) g.getEdgeWeight(edge3))));
        		  //  System.out.println("The current error is "+bl.getIndexInMethod()+" And "+bsucc.getIndexInMethod());
        			try
        			{
        		    units.insertOnEdge(st1, bl.getTail(), bsucc.getHead());
        			}
        			catch(Exception et)
        			{
        				
        			}
        		}
        	}
        }
        
		        // Assign global method offset the  value of totalnumber of  paths in a method
        
        
        
        int bid,nextnode=0;
      //  String str=null;
        

        	// write the str3 that is string of block ids to the file
          //  String str1="Testcases/project-2/tmpoutput/"+b.getMethod().getSignature();
           String str1=b.getMethod().getSignature(); 
   //        System.out.println(str1);
            try
            {
             FileOutputStream f=new FileOutputStream(str1);
             ObjectOutputStream out=new ObjectOutputStream(f);
             
             out.writeObject(g);
            
            }
            catch(Exception exp)
            {
         	   exp.printStackTrace();
            }
            //----- project-3-------start
          
       
            
        
            Chain units3=b.getUnits();
            Iterator stmt3=units3.snapshotIterator();
            
            // add field of main in hashMap map2
            SootMethod method=b.getMethod();
            String signature = method.getSignature();
            boolean isMain2 = signature.equals("void main(java.lang.String[])");
            while(stmt3.hasNext())
            {
            	Stmt st31=(Stmt) stmt3.next();
            	if(st31 instanceof InvokeStmt)
            	{
            		
            			
            			if(st31.toString().endsWith("void start()>()"))
            			{
            				
            				
            				VirtualInvokeExpr startexp=(VirtualInvokeExpr) ((InvokeStmt)st31).getInvokeExpr();
            			    Local thread=(Local) startexp.getBase();
            			    
            		
            			    units.insertBefore(Jimple.v().newAssignStmt(childthreadid, Jimple.v().newVirtualInvokeExpr((Local) thread,Scene.v().getMethod("<java.lang.Thread: long getId()>").makeRef())), st31);		
            			    
            				InvokeExpr addExpr= Jimple.v().newStaticInvokeExpr(addtomap.makeRef(),childthreadid);
            			   units.insertBefore(Jimple.v().newInvokeStmt(addExpr), st31);
            			 //   map2.put(threadname, value)
            			}
            	}
            }
           //------ project -3 ---------end
            
          
         Iterator stmt2=units.snapshotIterator();
      // int balllarusid=ballid;
        while(stmt2.hasNext())
        {
        	Stmt st2=(Stmt) stmt2.next();
        	if( (st2 instanceof ReturnStmt || st2 instanceof ReturnVoidStmt))
        	{
        		AssignStmt st8=Jimple.v().newAssignStmt(ballid, Jimple.v().newAddExpr(ballid, IntConstant.v(offset)));
       		 units.insertBefore(st8, st2);
        		
        		
        		String str34=b.getMethod().getSignature();
            	Stmt st31=Jimple.v().newAssignStmt(str32, StringConstant.v(str34));
            	units.insertBefore(st31, st2);
        		
        		InvokeExpr printexpr=Jimple.v().newStaticInvokeExpr(print2.makeRef(),str32,ballid,str33);
            	units.insertBefore(Jimple.v().newInvokeStmt(printexpr), st2);
            	
          
        	
        	// -------- projetc-3----
        	
         	//	InvokeExpr printexpr=Jimple.v().newStaticInvokeExpr(print2.makeRef());
	        //	units.insertBefore(Jimple.v().newInvokeStmt(printexpr), st2);
         		 
        	
        	
        	
        	
        	// --------- project-3 ---------
        	
        	}
            else if (st2 instanceof InvokeStmt)
            {
                InvokeExpr exitexp = (InvokeExpr) ((InvokeStmt)st2).getInvokeExpr();
                if (exitexp instanceof StaticInvokeExpr)
                {
                    SootMethod target = ((StaticInvokeExpr)exitexp).getMethod();
                    
                    if (target.getSignature().equals("<java.lang.System: void exit(int)>"))
                   {
                    	//InvokeExpr printexpr=Jimple.v().newStaticInvokeExpr(print2.makeRef());
                    	
                    	//units.insertBefore(Jimple.v().newInvokeStmt(printexpr), st2);
                    	
                  		 AssignStmt st8=Jimple.v().newAssignStmt(ballid, Jimple.v().newAddExpr(ballid, IntConstant.v(offset)));
                		 units.insertBefore(st8, st2);
                		 tmpRef1 = Jimple.v().newLocal("tmpRef1", RefType.v("java.io.PrintStream"));
                 		 b.getLocals().add(tmpRef1);
                 		 units.insertBefore(Jimple.v().newAssignStmt(tmpRef1, Jimple.v().newStaticFieldRef(Scene.v().getField("<java.lang.System: java.io.PrintStream out>").makeRef())), st2);
                 		 SootMethod print = Scene.v().getMethod("<java.io.PrintStream: void println(int)>");
                 		 units.insertBefore(Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(tmpRef1,print.makeRef(), ballid)),st2);
         
                   }
                }
            }   
        	
         }
        
        // Project -3 
     System.out.println(b.toString());
        
        

	
	
	
	
//	----------------my code ends-------------------------------------------------------------------------------

		for (Block block : cfg.getBlocks()) {
			graph.addVertex(block);
		}

		for (Block block : cfg.getBlocks()) {
			for (Block succ : cfg.getSuccsOf(block))
				graph.addEdge(block, succ);
		}

	

		return;
	}

	public void finish(String testcase) {

		VertexNameProvider<Block> id = new VertexNameProvider<Block>() {

			@Override
			public String getVertexName(Block b) {
				return String.valueOf("\"" + b.getBody().getMethod().getNumber() + " " + b.getIndexInMethod() + "\"");
			}
		};

		VertexNameProvider<Block> name = new VertexNameProvider<Block>() {

			@Override
			public String getVertexName(Block b) {
				String body = b.toString().replace("\'", "").replace("\"", "");
				return body;
			}
		};

		new File("sootOutput").mkdir();

		DOTExporter<Block, DefaultEdge> exporter = new DOTExporter<Block, DefaultEdge>(id, name, null);
		try {
			exporter.export(new PrintWriter("sootOutput/" + testcase + ".dot"), graph);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}

		return;
	}

}