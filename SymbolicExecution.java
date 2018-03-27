package e0210;


import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.PrintWriter;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentLinkedQueue;

import soot.Body;

import com.microsoft.z3.*;

import soot.Local;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AddExpr;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.ConditionExpr;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.DivExpr;
import soot.jimple.EqExpr;
import soot.jimple.GeExpr;
import soot.jimple.GtExpr;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.LeExpr;
import soot.jimple.LtExpr;
import soot.jimple.MulExpr;
import soot.jimple.NeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.RemExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.SubExpr;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.XorExpr;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ExceptionalBlockGraph;
import soot.util.Chain;

public class SymbolicExecution extends SceneTransformer {

	
	String project,testcase;
	public SymbolicExecution(String project1, String testcase1) {
		// TODO Auto-generated constructor stub
		project=project1;
		testcase=testcase1;
		
		
		
	}
	HashMap<String,String> ordervariables=new HashMap<>();
	
    HashMap<String,String> map1=new HashMap<>();
    HashMap<String,String> lockobjects=new HashMap<>();
    
    HashMap<String,Integer> staticfieldsmap=new HashMap<>();
    HashMap<String,Integer> localfieldsmap=new HashMap<>();
    HashMap<String,String> forkmap=new HashMap<>();
 
    HashMap<String,String> StaticReadOVar=new HashMap<>();   // to save order variable of static read used at readwrite constraints
    HashMap<String,String> laststmtofthread=new HashMap<>();
    
    HashMap<String,List<String>> lockmap=new HashMap<String,List<String>>();
    HashMap<String,List<String>> unlockmap=new HashMap<String,List<String>>();
    
    HashMap<String,HashMap<String,String>> writestatic=new HashMap<>();

    HashMap<String,HashMap<String,String>> readstatic=new HashMap<>();
    HashMap<Local,String> throbjtothrid=new HashMap<>();
    
    HashMap<String,List<String>> locksmap2=new HashMap<>();
    HashMap<String,String> lockmap2=new HashMap<>();
    
    LinkedList<String> allthreads=new LinkedList();
	LinkedList<String> llist=new LinkedList();
	HashMap<String,String> returnstmt=new HashMap<>();
	
	HashMap<String,Integer> symbTableforRW=new HashMap<>();
	HashMap<String,String> joinstmtmap=new HashMap<>();
	
	HashMap<String,Integer> numberofcallsmap=new HashMap<>();
	Context ctx = new Context(new HashMap<String, String>());
	Solver solver = ctx.mkSolver();

	String threadid="0";
	SootMethod m,meth;
	int stmtno=0;
	String previouspath=null;
	String currentpath=null;
	boolean didclint=false;
	int stmtsinclinit=0;
	String clinitpath=null;
	String mainreturnstmt=null;
	String alltuples=null;
	String returnlocal=null;
	@Override
	protected void internalTransform(String phaseName, Map<String, String> options) {

        /* 
        SceneTransformer vs BodyTransformer
        ===================================
        BodyTransformer is applied on all methods separately. It uses multiple 
        worker threads to process the methods in parallel.
        SceneTransformer is applied on the whole program in one go. 
        SceneTransformer uses only one worker thread.
        
        It is better to use SceneTransformer for this part of the project 
        because:
        1. During symbolic execution you may need to 'jump' from one method
        to another when you encounter a call instruction. This is easily 
        done in SceneTransformer (see below)
        2. There is only one worker thread in SceneTransformer which saves 
        you from having to synchronize accesses to any global data structures
        that you'll use, (eg data structures to store constraints, trace, etc)
        
        How to get method body?
        =======================
        Use Scene.v().getApplicationClasses() to get all classes and
        SootClass::getMethods() to get all methods in a particular class. You
        can search these lists to find the body of any method.
        
        */
        
	
	    llist.add("0");
	    allthreads.add("0");
	//    addfieldstomap();

	    
		String tuplesFile = "Testcases/" + project + "/processed-output/" + testcase + ".tuples";
		try {
			String tuples = new String(Files.readAllBytes(Paths.get(tuplesFile)));
			alltuples=tuples;
			
			
			
			Scanner sc=new Scanner(tuples);
			while(sc.hasNext())
			{
				String str1=sc.nextLine();
				
			//	System.out.println(str1);
				String[] str2=str1.split(",");
		       	String keytomap=str2[0]+","+str2[1];
	        	
	        	numberofcallsmap.put(keytomap, -1);
	        	
				String str3=str2[0]+","+str2[1]+","+str2[2];
				map1.put(str3, str1);
			}
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		      // initialize static fields with symbolic variables
	    for(SootClass class3:Scene.v().getApplicationClasses())
	    {
	    	if(class3.getName().toString().startsWith("jdk") || class3.getName().toString().startsWith("popUtil.PoP_Util"))
	    		continue;
	   // 	System.out.println(class3.getName().toString());
	    	for(SootField field:class3.getFields())
	    	{
	 
	    		if(field.isStatic())
	    		{
	    			staticfieldsmap.put(field.getName(),0);
	    		}
	    		
	    	}
	    }
		
		Value localarray[]=new Value[3];
	    
	    FileInputStream finput;
	    ObjectInputStream oout;
	    while(!llist.isEmpty())
	    {
	    	String tid=llist.remove();
	    	if(tid.equals("0"))
	    	{
	    		for(SootClass class1:Scene.v().getApplicationClasses())
	    		{
	    			for(SootMethod method:class1.getMethods())
	    			{
	    				if(!method.getSignature().startsWith("<popUtil.PoP_Util"))
	    				{
	    				if(method.getSignature().toString().contains("void main(java.lang.String[])"))
	    				{
	    					m=method;
	    					
	    				}
	    				if(method.getSignature().toString().contains("clinit"))
	    				{
	    				if(method.getSignature().startsWith("<test"))
	    				{
	    					meth=method;
	    				}
	    				}
	    				}
	    			}
	    		}
	    		traversemethod(tid,meth,localarray);
	        	traversemethod(tid,m,localarray);
	    	}
	    	else
	    	{
	    		for(SootClass class1:Scene.v().getApplicationClasses())
	    		{
	    			for(SootMethod method:class1.getMethods())
	    			{
	    				if(!method.getSignature().startsWith("<popUtil.PoP_Util"))
	    				{
	    				if(method.getSignature().toString().contains("void run()"))
	    				{
	    					m=method;
	    				}
	    				}
	    			}
	    		}
	    		traversemethod(tid,m,localarray);
	    	}
	  
	    	
	    }

	  //  System.out.println("Lockmap:"+lockmap);
	  ///  System.out.println("unLockmap:"+unlockmap);
	    
	 //   Addlockunlockconstraints();
	//    AddReadWriteConstraints();
	    ReadWrite2();
	    solver.add(ctx.mkGt(ctx.mkIntConst("O_0_0_1"), ctx.mkIntConst("O_0_0_0")));
	    ordervariables.put("O_0_0_0", "0, Begin");
	    solver.add(ctx.mkGe(ctx.mkIntConst("O_0_0_0"), ctx.mkInt(0)));
	    solver.add(ctx.mkGe(ctx.mkIntConst("O_0_0_1"), ctx.mkInt(0)));
	    // main return statement constraints
	    for(String returnstmt1:returnstmt.keySet())
	    {
	    	String returnorder=returnstmt.get(returnstmt1);
	    	solver.add(ctx.mkGt(ctx.mkIntConst(mainreturnstmt), ctx.mkIntConst(returnorder)));
	    }
	   // System.out.println(returnstmt);
	    for(String jointid:joinstmtmap.keySet())
	    {
	    	String returnorder=returnstmt.get(jointid);
	    	String joinorder=joinstmtmap.get(jointid);
	    	
	    	System.out.println("problem in adding to solver  :"+joinorder+" : "+returnorder);
	    	solver.add(ctx.mkGt(ctx.mkIntConst(joinorder),ctx.mkIntConst(returnorder)));
	    }
	    lockunlockconstraints();
System.out.println(solver);
System.out.println(ordervariables);
System.out.println(solver.check());

 Model model=solver.getModel();

 int noofvars=0;
// Map<String,String> treemap=new TreeMap<String,String>();
 Map<Integer,String> treemap1=new TreeMap<Integer,String>();
for(String var:ordervariables.keySet())
	{
		
		IntExpr a=(IntExpr)model.eval(ctx.mkIntConst(var), true);
	
		String key1=a.toString();
		int nn=Integer.parseInt(key1);
		if(treemap1.containsKey(nn))
		{  
			String data1=treemap1.get(nn);
			data1=data1.concat("@"+ordervariables.get(var));
			treemap1.put(nn, data1);
		}
		else
		{   
			treemap1.put(nn, ordervariables.get(var));
		}

	}
StringBuilder sb=new StringBuilder();
String globalTraceOutPath = "Testcases/" + project + "/processed-output/" + testcase + ".global_trace";

try {
	PrintWriter writer=new PrintWriter(globalTraceOutPath);
	for(int key1:treemap1.keySet())
	{
		
		
		String data2=treemap1.get(key1);
		if(data2.contains("@"))
		{
			String[] data3=data2.split("@");
			int in=0;
			while(in<data3.length)
			{
		//		out.println(data3[in]);
				System.out.println(key1+":"+data3[in]);
				writer.println(data3[in]);
				in++;
			}
		}
		else
		{
			System.out.println(key1+":"+data2);
			//out.println(data2);
			writer.println(data2);
		}
	}
	
	writer.close();	
} catch (IOException e) {
	// TODO Auto-generated catch block
	e.printStackTrace();
}
// for prject-4


//	out.close();


//StringBuilder sb=new StringBuilder();
//System.out.println(sb);
        /* 
        Perform the following for each thread T:
        1. Start with the first method of thread T. If T is the main thread,
        the first method is main(), else it is the run() method of the thread's
        class
        2. Using (only) the tuples for thread T, walk through the code to 
        reproduce the path followed by T. If thread T performs method calls
        then, during this walk you'll need to jump from one method's body to 
        another to imitate the flow of control (as discussed during the Project session)
        3. While walking through the code, collect the intra-thread trace for 
        T and the path constraints.
        Don't forget that you need to renumber each dynamic instance of a static
        variable (i.e. SSA)
        */
	    return;
	}
	protected void traversemethod(String tid,SootMethod method,Value arlocal[])
	{
		
		if(method.getName().toString().contains("run") || method.getName().toString().contains("main"))
		{
			System.out.println(tid+",Begin");

		}
	//	System.out.println("method name is"+method.getSignature());
		if(method.getSignature().toString().startsWith("<popUtil.PoP_Util"))
		{	return;		
		}
		int numberofstarts=0;
		Body b=method.getActiveBody();

		ExceptionalBlockGraph cfg=new ExceptionalBlockGraph(b);
		int nocalls=numberofcallsmap.get(method.getSignature()+","+tid);
		nocalls=nocalls+1;
		numberofcallsmap.put(method.getSignature()+","+tid, nocalls);
		String tuplekey=method.getSignature()+","+tid+","+nocalls;
		
	//	System.out.println(tuplekey);
		String tuple=map1.get(tuplekey);

	//	String previouspath=null;
	//	String currentpath=null;
		String[] tuplefields=tuple.split(",");
 		String[] blockids=tuplefields[3].split("->"); 
 		    int i=0;
		    int blockid;
		   Chain ch=b.getLocals();
		   Iterator it=ch.snapshotIterator();
			   while(it.hasNext())
		   {
			   String str=it.next().toString();
			   if(!localfieldsmap.containsKey(str+"_"+tid))
			   {
			   localfieldsmap.put(str+"_"+tid, 0);
			   }
		   }
	      while(i<blockids.length)
		      {
			      blockid=Integer.parseInt(blockids[i]);
			
			      for(Block block:cfg.getBlocks())
			      {
			    	  if(blockid==block.getIndexInMethod())
			    	  {
			    	   Body bodyofblock=block.getBody();
			    	   Chain units=(Chain) bodyofblock.getUnits();
			    	   Unit head=block.getHead();
			    	   Unit tail=block.getTail();
			    	   Iterator stmtIt = units.iterator(block.getHead(),block.getTail());
			    	   
			    
			    	   while(stmtIt.hasNext())
			    	   {
			    		   Stmt stmt=(Stmt) stmtIt.next();
			    		
			    		  if(stmt instanceof IdentityStmt)
			    		  {
			    			//  DefinitionStmt stmtd=(DefinitionStmt) stmt;
			    			  Value value=((IdentityStmt) stmt).getRightOp();
			    				  if(value instanceof ParameterRef)
			    				  {
			    					//  System.out.println(stmt);	  
			    				int paramindex=((ParameterRef) value).getIndex();
			    				Value paramvalue=arlocal[paramindex];
			    				if(paramvalue instanceof Constant)
			    				{
			    					String left_symb_name=getSymbNameLocal(((IdentityStmt) stmt).getLeftOp().toString(),tid);
			    					int intparamvalue=Integer.parseInt(paramvalue.toString());
			    					solver.add(ctx.mkEq(ctx.mkIntConst(left_symb_name), ctx.mkInt(intparamvalue)));
			    					
			    				}
			    				else if(paramvalue instanceof Local)
			    				{
			    					String left_symb_name=getSymbNameLocal(((IdentityStmt) stmt).getLeftOp().toString(),tid);
			    					String right_symb_name=getSymbNameLocalRead(paramvalue.toString(),tid);
			    					solver.add(ctx.mkEq(ctx.mkIntConst(left_symb_name), ctx.mkIntConst(right_symb_name)));
			    					System.out.println("local is :"+paramvalue);
			    				}
			    				  }
			    			  
			    		  }
			    		  if(stmt instanceof AssignStmt)
			    		  {
			    			 
       			    		  Value leftop;
       			    		  Value rightop;
			    			leftop=((AssignStmt) stmt).getLeftOp();
			    			rightop=((AssignStmt) stmt).getRightOp();
			    			if(rightop instanceof  StaticInvokeExpr)
			    			{
			
			    				String type=rightop.getType().toString();
			    				
			    				if(type.contains("Integer") || type.contains("Boolean") || type.contains("Character") || type.contains("Long") || 
			    						type.contains("String") || type.contains("int") || type.contains("boolean"))
			    				{
			    					
			    					String methodcallname=((StaticInvokeExpr) rightop).getMethod().getName();
			    					if(alltuples.contains(methodcallname))
			    					{
			    						InvokeExpr invokeexp=(InvokeExpr) rightop;
			    						SootMethod newmethod1=invokeexp.getMethod();
			    						
			    						stmtno++;
			    						int nextstmtno=stmtno+1;
			    						String nextstmt="O_"+tid+"_"+tuplefields[2]+"_"+nextstmtno;
			    						 currentpath="O_"+tid+"_"+tuplefields[2]+"_"+stmtno;
			    						   System.out.println(currentpath+"="+newmethod1.getSignature());
			    						   Expr current=ctx.mkIntConst(currentpath);
			    						   Expr next=ctx.mkIntConst(nextstmt);
			    						   if(previouspath!=null)
			    						   {
			    							   Expr previous=ctx.mkIntConst(previouspath);
			    							   solver.add(ctx.mkGt((ArithExpr)current, (ArithExpr)previous));
			    								solver.add(ctx.mkGe((ArithExpr)current, ctx.mkInt(0)));
			    							 	solver.add(ctx.mkGe((ArithExpr)previous, ctx.mkInt(0)));
			    						   }
			    						   previouspath=currentpath;
			    						   int argcount=invokeexp.getArgCount();
			    						   Value arrayl[]=new Value[3];
			    						   for(int count=0;count<argcount;count++)
			    						   {
			    							   Value arg=invokeexp.getArg(count);
			    							   arrayl[count]=arg;
			    						   }
			    						   traversemethod(tid,newmethod1,arrayl);
			    						   String right_local_symb=getSymbNameLocalRead(returnlocal,tid);
			    						   String left_local_symb=getSymbNameLocal(leftop.toString(),tid);
			    						   solver.add(ctx.mkEq(ctx.mkIntConst(right_local_symb), ctx.mkIntConst(left_local_symb)));
			    					//	System.out.println("yes method is from calledd"+methodcallname);
			    					}
			    					else
			    					{
			    					int val;
			    					//int val=Integer.parseInt(rightop.toString().substring(rightop.toString().lastIndexOf("(")+1, rightop.toString().lastIndexOf(")")));
			    				
			    					Value val2=((StaticInvokeExpr) rightop).getArg(0);
			    				//	System.out.println("static is :---"+rightop);
			    					if(val2 instanceof IntConstant)
			    					{
			    						val=((IntConstant) val2).value;
			    						Expr numeric=ctx.mkNumeral(val, ctx.mkIntSort());
				    					String symb_name_local=getSymbNameLocal(leftop.toString(),tid);
				    				//	System.out.println(symb_name_local);
				    				//	System.out.println(localfieldsmap.get(leftop.toString()+"_"+tid));
				    					solver.add(ctx.mkEq(ctx.mkIntConst(symb_name_local), numeric));
			    					}
			    					else if(val2 instanceof Local)
			    					{
			    					//	System.out.println("yeah handling with parameters  and value is :");
			    						if(val2.getType().toString().contains("int"))
			    						{
			    						String symb_name=getSymbNameLocalRead(val2.toString(),tid);
			    						String symb_name_left=getSymbNameLocal(leftop.toString(),tid);
				    					Expr ex3=ctx.mkIntConst(symb_name_left);
				    					solver.add(ctx.mkEq(ex3, ctx.mkIntConst(symb_name)));
			    						}
			    						else if(val2.getType().toString().contains("java.lang.String"))
			    						{
			    							
			    							Stmt st=(Stmt) block.getPredOf(stmt);
			    							Value ind=st.getArrayRef().getIndex();
			    							int index=Integer.parseInt(ind.toString());
			    							String argsFile = "Testcases/" + project + "/input/" + testcase;
			    							String testcaseArgs;
											try {
												
												testcaseArgs = new String(Files.readAllBytes(Paths.get(argsFile)));
												  String[] args=testcaseArgs.split(" ");
		                                             int val3=Integer.parseInt(args[index]);
		                                             String symb_name_local=getSymbNameLocal(leftop.toString(),tid);
		                                             
		                                             solver.add(ctx.mkEq(ctx.mkIntConst(symb_name_local), ctx.mkInt(val3)));
		                                            //		System.out.println(val3);
											} catch (IOException e) {
												// TODO Auto-generated catch block
												e.printStackTrace();
											}
                                           
			    						}
			    					}
			    					}
			    				}
			    				else if(type.contains("Float") || type.contains("Double"))
			    				{
			    					double val=Double.parseDouble(rightop.toString().substring(rightop.toString().lastIndexOf("(")+1, rightop.toString().lastIndexOf(")")));
			    					String symb_name_local=getSymbNameLocal(leftop.toString(),tid);
			    			//		solver.add(ctx.mkEq(ctx.mkRealConst(symb_name_local), ctx.mkNumeral(val,ctx.mkRealSort())));  // please solve i5t later...
			    				}
			    				
			    				
			    			}
			    			
			    			if(rightop instanceof VirtualInvokeExpr)
			    			{
			    			//	System.out.println("Right side is virtualInvoke :"+rightop);
			    				String type=rightop.getType().toString();
			    				//System.out.println(type);
			    				
			    				if(type.contains("int") || type.contains("boolean"))
			    				{
			    					System.out.println("the virtual invoke is :"+rightop);
			    					VirtualInvokeExpr expression=(VirtualInvokeExpr) rightop;
			    					String base=expression.getBase().toString();
			    					String symb_name_left=getSymbNameLocal(leftop.toString(),tid);
			    					String symb_name_right=getSymbNameLocalRead(base,tid);
			    					solver.add(ctx.mkEq(ctx.mkIntConst(symb_name_left), ctx.mkIntConst(symb_name_right)));
			    			}
			    			}
			    			if(leftop instanceof StaticFieldRef || rightop instanceof StaticFieldRef)
			    			{
			    				  if(rightop instanceof StaticFieldRef)
			    				  {
			    					  if(rightop.getType().toString().equals("java.util.concurrent.locks.Lock"))
			    					  {
			    						String lockname=Returnobject(rightop.toString());
			    					//	System.out.println("left operator is :"+leftop.toString());
	 		    						lockobjects.put(leftop.toString(), rightop.toString());
			    					//	System.out.println("lock obj:"+leftop+" And name is :"+lockobj);
			    					  }
			    				  }
					    	
			    				  if(leftop instanceof StaticFieldRef)
			    				  {
		
			    					  String varname=Returnobject(leftop.toString());
			    				//	  System.out.println("Vaariable name is "+varname+" And method name is:"+method.getName()+" And class is:"+method.getClass());
			    					  int version=staticfieldsmap.get(varname);
			    					  version++;
			    					  staticfieldsmap.put(varname,version);
			    					  String symbname=varname+"_"+version;
			    					//  System.out.println("Heeeeloo");
			    					//  System.out.println(leftop.getType()+":"+leftop);
			    					  String gtrace=tid+", Write, "+leftop;    // to use at final global trace
			    					  if(leftop.getType().toString().equals("java.lang.Integer") || leftop.getType().toString().equals("java.lang.Boolean")
					    					  || leftop.getType().toString().equals("java.lang.Byte") || leftop.getType().toString().equals("java.lang.Long") || 
					    					  leftop.getType().toString().equals("java.lang.Character"))
			    					  {
			    						  String symb_name_local=rightop.toString()+"_"+tid+"_"+localfieldsmap.get(rightop.toString()+"_"+tid);
			    						  solver.add(ctx.mkEq(ctx.mkIntConst(symbname), ctx.mkIntConst(symb_name_local)));
					    				 currentpath="O_"+tid+"_"+tuplefields[2]+"_";
							    		 stmtno++;
							    		 currentpath=currentpath.concat(""+stmtno);
							    		 System.out.println(currentpath+"="+tid+", Write,"+varname+", "+symbname);
							    		 ordervariables.put(currentpath, gtrace);      // to use at final global trace
							    		 // adding write variable to hashmap
							    		 if(writestatic.containsKey(varname))
							    		 {
							    			 HashMap<String,String> writevars=writestatic.get(varname);
							    			 writevars.put(symbname, currentpath);
							    		 }
							    		 else
							    		 {
							    			 HashMap<String,String> writevars=new HashMap<>();
							    			 writevars.put(symbname, currentpath);
							    			 writestatic.put(varname, writevars);
							    		 }
							    		 if(previouspath!=null)
							    		 {
						    				Expr exp1=ctx.mkIntConst(currentpath);
						    				Expr exp2=ctx.mkIntConst(previouspath);
						    				solver.add(ctx.mkGt((ArithExpr)exp1,(ArithExpr) exp2));
						    				solver.add(ctx.mkGe((ArithExpr)exp1, ctx.mkInt(0)));
						    				solver.add(ctx.mkGe((ArithExpr)exp1, ctx.mkInt(0)));
						     		 } 			
							    		 previouspath=currentpath;
			    					  }
					    			 
					    			 else if(leftop.getType().toString().equals("java.lang.Double") || leftop.getType().toString().equals("java.lang.Float"))
					    			 {
					    				 currentpath="O_"+tid+"_"+tuplefields[2]+"_";
							    		 stmtno++;
							    		 currentpath=currentpath.concat(""+stmtno);
							    		 ordervariables.put(currentpath, gtrace);      // to use at final global trace
					    				 String newLeftop=leftop.toString().concat(""+0);
					    				 String symb_name_local=rightop.toString()+"_"+tid+"_"+localfieldsmap.get(rightop.toString()+"_"+tid);
					    				 solver.add(ctx.mkEq(ctx.mkRealConst(symbname), ctx.mkRealConst(symb_name_local)));
					    				if(previouspath!=null)
						    			{
						    				//solver.add(ctx.mkle(previouspath, currentpath));
						    				ArithExpr exp1=ctx.mkIntConst(currentpath);
						    				ArithExpr exxp=ctx.mkIntConst(previouspath);
						    				solver.add(ctx.mkGt(exp1,exxp));
						    				solver.add(ctx.mkGe((ArithExpr)exp1, ctx.mkInt(0)));
						    				solver.add(ctx.mkGe((ArithExpr)exxp, ctx.mkInt(0)));
						  			}
					    				previouspath=currentpath;
					    			}
					    			 
			    				  }      // if(leftop instanceof StaticFieldRef) ends
			    				  else if(rightop instanceof StaticFieldRef)
			    				  {
			    					//  System.out.println(leftop.getType()+":"+leftop);
			 		    			 if(rightop.getType().toString().equals("java.lang.Integer") || rightop.getType().toString().equals("java.lang.Boolean")
					    					  || rightop.getType().toString().equals("java.lang.Byte") || rightop.getType().toString().equals("java.lang.Long") || 
					    					  rightop.getType().toString().equals("java.lang.Character"))
			 		    			 {
			 		    				 
			 		    			   
			 		    				  String varname=Returnobject(rightop.toString());
				    					  int version=staticfieldsmap.get(varname);
				    					  version++;
				    					  staticfieldsmap.put(varname,version);
				    					  String symbname=varname+"_"+version;
				    					  
				    					  String gtrace=tid+", Read, "+rightop;
				    					  
				    					  currentpath="O_"+tid+"_"+tuplefields[2]+"_";
				    					  stmtno++;
				    					  currentpath=currentpath.concat(""+stmtno);
				    					  System.out.println(currentpath+"="+tid+", Read, "+varname+", "+symbname);
				    					  ordervariables.put(currentpath, gtrace);
				    					  StaticReadOVar.put(symbname, currentpath);
				    					  if(readstatic.containsKey(varname))
								    		 {
								    			 HashMap<String,String> readvars=readstatic.get(varname);
								    			 readvars.put(symbname, currentpath);
								    		 }
								    		 else
								    		 {
								    			 HashMap<String,String> readvars=new HashMap<>();
								    			 readvars.put(symbname, currentpath);
								    			 readstatic.put(varname, readvars);
								    		 }
				    					  if(previouspath!=null)
				    					  {
				    						//  System.out.println("making "+currentpath+"Int constant");
				    						  ArithExpr exp1=ctx.mkIntConst(currentpath);
				    						  ArithExpr exp2=ctx.mkIntConst(previouspath);
				    						  solver.add(ctx.mkGt(exp1, exp2));
				    						  solver.add(ctx.mkGe((ArithExpr)exp1, ctx.mkInt(0)));
				    						  solver.add(ctx.mkGe((ArithExpr)exp2, ctx.mkInt(0)));
				    					  }
				    		
				    					  String symb_local=getSymbNameLocal(leftop.toString(),tid);
				    					//  System.out.println(symb_local);
				    					  solver.add(ctx.mkEq(ctx.mkIntConst(symb_local), ctx.mkIntConst(symbname)));
				    				  previouspath=currentpath;
			 		    			 }
			 		    			 else if(rightop.getType().toString().equals("java.lang.Double") || rightop.getType().toString().equals("java.lang.Float"))
			 		    			 {
			 		    				  String varname=Returnobject(rightop.toString());
				    					  int version=staticfieldsmap.get(varname);
				    					  version++;
				    					  staticfieldsmap.put(varname,version);
				    					  String symbname=varname+"_"+version;
				    					  System.out.println(tid+", Read, "+varname+", "+symbname);
				    					  String gtrace=tid+", Read, "+rightop+", "+symbname;
				    					  currentpath="O_"+tid+"_"+tuplefields[2]+"_";
				    					  stmtno++;
				    					  currentpath=currentpath.concat(""+stmtno);
				    					  ordervariables.put(currentpath, gtrace);
				    					  StaticReadOVar.put(symbname, currentpath);
				    					  if(previouspath!=null)
				    					  {
				    						  Expr exp1=ctx.mkIntConst(currentpath);
				    						  Expr exp2=ctx.mkIntConst(previouspath);
				    						  solver.add(ctx.mkGt((ArithExpr)exp1,(ArithExpr)exp2));
				    						  solver.add(ctx.mkGe((ArithExpr)exp1, ctx.mkInt(0)));
				    						  solver.add(ctx.mkGe((ArithExpr)exp2, ctx.mkInt(0)));
				    					  }
				    					  int localversion=localfieldsmap.get(leftop.toString()+"_"+tid);
				
				    					  localversion++;
				    					  localfieldsmap.put(leftop.toString()+tid, localversion);
				    					  String symb_local=getSymbNameLocal(leftop.toString(),tid);
				    					  solver.add(ctx.mkEq(ctx.mkRealConst(symb_local), ctx.mkRealConst(symbname)));
				    					  previouspath=currentpath;
			 		    			 }
			    				  }	// else if(rightop instanceof StaticFieldRef) ends
			    			
			    			}
			    			else if(leftop instanceof Local)
			    			{
			    				if(rightop instanceof BinopExpr)
			    				{
			    				
			    					BinopExpr biexp=(BinopExpr) rightop;
			    					Value op1=biexp.getOp1();
			    					Value op2=biexp.getOp2();
			    					Expr ex1;
			    					Expr ex2;
			    				
			    					if(op1 instanceof Local)
			    					{
			    						
			    						String symb_name=getSymbNameLocalRead(op1.toString(),tid);
			    						ex1=ctx.mkIntConst(symb_name);
			    					}
			    					else
			    					{
			    						int val=Integer.parseInt(op1.toString());
			    						ex1=ctx.mkInt(val);
			    					}
			    					if(op2 instanceof Local)
			    					{
			    						String symb_name2=getSymbNameLocalRead(op2.toString(),tid);
			    						ex2=ctx.mkIntConst(symb_name2);
			    					}
			    					else
			    					{
			    						int val2=Integer.parseInt(op2.toString());
			    						ex2=ctx.mkInt(val2);
			    					}
			    					String symb_name_left=getSymbNameLocal(leftop.toString(),tid);
			    					
			    					Expr ex3=ctx.mkIntConst(symb_name_left);
			    				//	System.out.println(ex3);
			    					if(biexp instanceof AddExpr){
			    						solver.add(ctx.mkEq(ex3, ctx.mkAdd((ArithExpr)ex1,(ArithExpr)ex2)));
			    					}
			    					else if(biexp instanceof MulExpr){
			    						solver.add(ctx.mkEq(ex3, ctx.mkMul((ArithExpr)ex1,(ArithExpr)ex2)));
			    					}
			    					else if(biexp instanceof SubExpr){
			    						solver.add(ctx.mkEq(ex3, ctx.mkSub((ArithExpr)ex1,(ArithExpr)ex2)));
			    					}
			    					else if(biexp instanceof DivExpr){
			    						solver.add(ctx.mkEq(ex3, ctx.mkDiv((ArithExpr)ex1,(ArithExpr) ex2)));
			    					}
			    					else if(biexp instanceof RemExpr)
			    					{
			    						solver.add(ctx.mkEq(ex3, ctx.mkRem((IntExpr)ex1,(IntExpr) ex2)));
			    					}
			    					else if(biexp instanceof XorExpr)
			    					{
			    						String symb_name=getSymbNameLocalRead(op1.toString(),tid);
			    						BitVecExpr bexp1=ctx.mkInt2BV(32,ctx.mkIntConst(symb_name));
			    						BitVecExpr bexp2=ctx.mkBV((Integer.parseInt(op2.toString())), 32);
			    					
			    						BitVecExpr bexp=ctx.mkBVXOR(bexp1, bexp2);
			    						System.out.println("xor--------------"+bexp);
			    						solver.add(ctx.mkEq(ex3, ctx.mkBV2Int(bexp, true)));
			    						
			    						//solver.add(ctx.mkEq(ex3,ctx.mkXor((BoolExpr)ex1, (BoolExpr)ex2)));
			    					}
			    				}
			    				else if(rightop instanceof Local)
			    				{
			    					String symb_name_r=getSymbNameLocalRead(rightop.toString(),tid);
			    					String symb_name_l=getSymbNameLocal(leftop.toString(),tid);
			    					Expr ex1=ctx.mkIntConst(symb_name_l);
			    					Expr ex2=ctx.mkIntConst(symb_name_r);
			    					solver.add(ctx.mkEq(ex1, ex2));
			    				}
			    				else if(rightop instanceof Constant)
			    				{
			    					String symb_name_l=getSymbNameLocal(leftop.toString(),tid);
			    					System.out.println("adding "+symb_name_l);
			    					int num=Integer.parseInt(rightop.toString());
			    					solver.add(ctx.mkEq(ctx.mkIntConst(symb_name_l), ctx.mkInt(num)));
			    				}
			    					
			    			}
			    		
			    	
			    		  }  //  if(stmt instanceof AssignStmt)    ends
			    		  
			    		  if(stmt instanceof IfStmt)
			    		  {
			    			  int nextblockid;
			       			  Value condition=((IfStmt) stmt).getCondition();
			       			//  System.out.println(condition);
	    					  nextblockid=Integer.parseInt(blockids[i+1]);
	    					//  System.out.println("current block id:"+blockid+" and next blockid is :"+nextblockid);
	    					  if(nextblockid==blockid+1 || nextblockid<=blockid)
	    					  {
	    						  ifConstraints(condition,true,tid);
	    						  
	    					  }
	    					  else
	    						  ifConstraints(condition,false,tid);

			    			  
			    		  }
			    		  if(stmt instanceof ReturnStmt || stmt instanceof ReturnVoidStmt)
			    		  {
			    			  if(method.getSignature().contains("main") || method.getSignature().contains("run"))
			    			  {
			    				  
			    				  currentpath="O_"+tid+"_"+tuplefields[2]+"_";
		    					  stmtno++;
		    					  currentpath=currentpath.concat(""+stmtno);
		    					  System.out.println(currentpath+"="+tid+", Ends");
		    					  if(method.getName().toString().contains("main"))
		    					  {
		    						  ordervariables.put(currentpath, "0, End");
		    						  mainreturnstmt=currentpath;
		    					  }
		    					  else
		    					  {
		    						  String gtrace=tid+", End";   // for final global trace
					    				ordervariables.put(currentpath, gtrace);
					    				returnstmt.put(tid, currentpath);
					    				
		    					  }
		    					  if(previouspath!=null)
		    					  {
		    						  Expr exp11=ctx.mkIntConst(currentpath);
		    						  Expr exp12=ctx.mkIntConst(previouspath);
		    						  solver.add(ctx.mkGt((ArithExpr)exp11,(ArithExpr)exp12));
		    						  solver.add(ctx.mkGe((ArithExpr)exp11, ctx.mkInt(0)));
		    						  solver.add(ctx.mkGe((ArithExpr)exp12, ctx.mkInt(0)));
		    					  }
			    				  stmtno=0;
			    				  previouspath=null;
			    				  currentpath=null;
			    			  }
			    			  else
			    			  {
			    				  currentpath="O_"+tid+"_"+tuplefields[2]+"_";
		    					  stmtno++;
		    					  currentpath=currentpath.concat(""+stmtno);
		    					  if(previouspath!=null)
		    					  {
		    						  Expr exp11=ctx.mkIntConst(currentpath);
		    						  Expr exp12=ctx.mkIntConst(previouspath);
		    						  solver.add(ctx.mkGt((ArithExpr)exp11,(ArithExpr)exp12));
		    						  solver.add(ctx.mkGe((ArithExpr)exp11, ctx.mkInt(0)));
		    						  solver.add(ctx.mkGe((ArithExpr)exp12, ctx.mkInt(0)));
		    						
		    					  }
		    					  if(!(stmt instanceof ReturnVoidStmt))
		    					  {
		    						  ReturnStmt rstmt=(ReturnStmt) stmt;
		    						  Local returnvalue1=(Local) rstmt.getOp();
		    						  returnlocal=returnvalue1.toString();
		    					  }
			    			  }
			    		  }
			    		  if(stmt instanceof InvokeStmt)
			    			   {

			    				   if(stmt.toString().endsWith("void start()>()"))
			    					{
			    						 currentpath="O_"+tid+"_"+tuplefields[2]+"_";
							    		 stmtno++;
							    		// System.out.println(stmtno);
							    		 currentpath=currentpath.concat(""+stmtno);
			    					     threadid=tid+"."+numberofstarts;
			    					     numberofstarts++;
			    					     llist.add(threadid);
			    					     allthreads.add(threadid);
			    					     VirtualInvokeExpr startexp=(VirtualInvokeExpr) ((InvokeStmt)stmt).getInvokeExpr();
			            			     Local thread=(Local) startexp.getBase();
			    					     forkmap.put(threadid, currentpath);
			    					     throbjtothrid.put(thread,threadid);
			    					     String firststmt="O_"+threadid+"_"+0+"_"+0;
			    					     String secondstmt="O_"+threadid+"_"+0+"_"+1;
			    					//     addlaststmtofthread(threadid);
			    					     System.out.println(currentpath+"="+tid+", Fork, "+threadid);
			    					     String gtrace=tid+", Fork, "+threadid;     // for finla global trace
			    					     String gtrace2=threadid+", Begin";
			    					     ordervariables.put(firststmt,gtrace2);
			    					     ordervariables.put(currentpath, gtrace);
			    					//   System.out.println("threadid of new thread is :"+threadid);
			    					     Expr current=ctx.mkIntConst(currentpath);
		    					     		Expr exstart=ctx.mkIntConst(firststmt);
		    					     		Expr secondexp=ctx.mkIntConst(secondstmt);
			    					     	if(previouspath!=null)
			    					     	{
			    					     		Expr previous=ctx.mkIntConst(previouspath);
			    					     		solver.add(ctx.mkGt((ArithExpr)current,(ArithExpr)previous));
			    					     		solver.add(ctx.mkGe((ArithExpr)current, ctx.mkInt(0)));
			    					     		solver.add(ctx.mkGe((ArithExpr)exstart, ctx.mkInt(0)));
			    					     		solver.add(ctx.mkGe((ArithExpr)previous, ctx.mkInt(0)));
			    					     	}
			    					     	solver.add(ctx.mkGt((ArithExpr)exstart, (ArithExpr)current));
			    					     	solver.add(ctx.mkGt((ArithExpr)secondexp, (ArithExpr)exstart));
			    					 		solver.add(ctx.mkGe((ArithExpr)secondexp, ctx.mkInt(0)));
			    					 	
			    					     	if(threadid.equals("0.0"))   // to patchup clinit with main
					    					     {
					    					    	 String dummy="O_"+tid+"_"+tuplefields[2]+"_"+(stmtno-1);
					    					    	 solver.add(ctx.mkGt(ctx.mkIntConst(currentpath), ctx.mkIntConst(dummy)));
					    					     }
			    					     previouspath=currentpath;
			    					}
			    				   else if(stmt.toString().endsWith("void join()>()"))
			    				   {
			    						 currentpath="O_"+tid+"_"+tuplefields[2]+"_";
							    		 stmtno++;
							    		 currentpath=currentpath.concat(""+stmtno);
				 					     VirtualInvokeExpr joinexp=(VirtualInvokeExpr) ((InvokeStmt)stmt).getInvokeExpr();
			            			     Local threadname=(Local) joinexp.getBase();
			            			    // System.out.println(threadname);
							    		 String threadid=throbjtothrid.get(threadname);
		
							    		// String laststmt=laststmtofthread.get(threadid);
							    	//	 System.out.println("last statement :"+laststmt);
							    		 if(previouspath!=null)
							    		 {
							 	     		Expr current=ctx.mkIntConst(currentpath);
		    					     ///		Expr joinstmt=ctx.mkIntConst(laststmt);
		    					     		Expr previous=ctx.mkIntConst(previouspath);
		    					     //		solver.add(ctx.mkGt((ArithExpr)current,(ArithExpr)joinstmt));
		    					     		solver.add(ctx.mkGt((ArithExpr)current, (ArithExpr)previous));
		    					     		solver.add(ctx.mkGe((ArithExpr)current, ctx.mkInt(0)));
		    					     //		solver.add(ctx.mkGe((ArithExpr)joinstmt, ctx.mkInt(0)));
		    					     		solver.add(ctx.mkGe((ArithExpr)previous, ctx.mkInt(0)));
		    					     		
							    		 }
							    		 System.out.println(currentpath+"="+tid+",Join , "+threadid);
							    		 String gtrace=tid+", Join, "+threadid;
							    		 ordervariables.put(currentpath, gtrace);
							    		 joinstmtmap.put(threadid, currentpath);
							    		 previouspath=currentpath;
			    				   }
			    				   else if(stmt.toString().endsWith("void lock()>()"))
			    				   {
			    					     currentpath="O_"+tid+"_"+tuplefields[2]+"_";
							    		 stmtno++;
							    		 currentpath=currentpath.concat(""+stmtno);
							    		 InterfaceInvokeExpr expr= (InterfaceInvokeExpr) stmt.getInvokeExpr();
							    		 Local lockobj=(Local) expr.getBase();
							    	         System.out.println(currentpath+"="+tid+",Lock, "+lockobjects.get(lockobj.toString()));
							    	         String gtrace=tid+", Lock, "+lockobjects.get(lockobj.toString());
							    	         ordervariables.put(currentpath, gtrace);
							    	         String lockname=lockobjects.get(lockobj.toString());
							    	         if(lockmap.containsKey(lockname))
							    	         {
							    	        	 lockmap.get(lockname).add(currentpath);
							    	         }
							    	         else						// 8600536448
							    	         {
							    	        		List<String> ordervars=new ArrayList<String>();
							    	        		ordervars.add(currentpath);
							    	        		lockmap.put(lockname, ordervars);
							    	         }
							    
							    	   //      System.out.println("First statement is :"+previouspath);
							    	         if(previouspath!=null)
							    	     {
							    	    	Expr current=ctx.mkIntConst(currentpath);
							    	     	Expr previous=ctx.mkIntConst(previouspath);
							    	     	solver.add(ctx.mkGt((ArithExpr)current, (ArithExpr)previous));
							    	     	solver.add(ctx.mkGe((ArithExpr)current, ctx.mkInt(0)));
							    	     	solver.add(ctx.mkGe((ArithExpr)previous, ctx.mkInt(0)));
							    	     
							    	     }
							    	        
							    	         lockmap2.put(lockname, currentpath);
							    		 previouspath=currentpath;
			    				   }
			    				   else if(stmt.toString().endsWith("void unlock()>()"))
			    				   {
			    					   currentpath="O_"+tid+"_"+tuplefields[2]+"_";
							    	   stmtno++;
							    	   currentpath=currentpath.concat(""+stmtno);
							    		 InterfaceInvokeExpr unlockexpr= (InterfaceInvokeExpr) stmt.getInvokeExpr();
								    	    
						    	         Local unlockobj=(Local) unlockexpr.getBase();
						    	         System.out.println(currentpath+"="+tid+", Unlock, "+lockobjects.get(unlockobj.toString()));
						    	         String gtrace=tid+", Unlock, "+lockobjects.get(unlockobj.toString());
						    	         ordervariables.put(currentpath, gtrace);
						    	         String lockname=lockobjects.get(unlockobj.toString());
						    	         if(unlockmap.containsKey(lockname))
						    	         {
						    	        	 unlockmap.get(lockname).add(currentpath);
						    	         }
						    	         else
						    	         {
						    	        		List<String> ordervarsunlock=new ArrayList<String>();
						    	        		ordervarsunlock.add(currentpath);
						    	        		unlockmap.put(lockname, ordervarsunlock);
						    	         }
						    	         if(previouspath!=null)
						    	         {
						    	        	 Expr current=ctx.mkIntConst(currentpath);
						    	        	 Expr previous=ctx.mkIntConst(previouspath);
						    	        	 solver.add(ctx.mkGt((ArithExpr)current, (ArithExpr)previous));
						    	        		solver.add(ctx.mkGe((ArithExpr)current, ctx.mkInt(0)));
								    	     	solver.add(ctx.mkGe((ArithExpr)previous, ctx.mkInt(0)));
								    	     
						    	         } 
						    	         String lockordervariable=lockmap2.get(lockname);
						    	         String lockunlock=lockordervariable+"#"+currentpath;
						    	         lockmap2.remove(lockname);
						    	         if(locksmap2.containsKey(lockname))
						    	         {
						    	        	 List<String> listoflocks=new ArrayList<>();
						    	        	 listoflocks=locksmap2.get(lockname);
						    	        	 listoflocks.add(lockunlock);
						    	        	 locksmap2.put(lockname, listoflocks);
						    	         }
						    	         else
						    	         {
						    	        	 List<String> listoflocks=new ArrayList<>();
						    	        	 listoflocks.add(lockunlock);
						    	        	 locksmap2.put(lockname, listoflocks);
						    	         }
							    	   previouspath=currentpath;
			    				   }
			    				   else
			    				   {
			    					   
		    					   InvokeExpr expr=stmt.getInvokeExpr();
			    				   SootMethod newmethod=expr.getMethod();
			    				   
			    				   if(!newmethod.getSignature().endsWith("<init>()>"))
			    				   {
			    					   if( !newmethod.getSignature().startsWith("<java"))
			    					   {
			    						   if(!newmethod.getSignature().startsWith("<popUtil.PoP_Util"))
			    						   {
			    					   System.out.println("calling : "+newmethod.getSignature()); 
			    					   
			    					   stmtno++;
			    					   int nextstmtno=stmtno+1;
			    					   String nextstmt="O_"+tid+"_"+tuplefields[2]+"_"+nextstmtno;
			    					   currentpath="O_"+tid+"_"+tuplefields[2]+"_"+stmtno;
			    					   System.out.println(currentpath+"="+newmethod.getSignature());
			    					   Expr current=ctx.mkIntConst(currentpath);
			    					   Expr next=ctx.mkIntConst(nextstmt);
					    	           if(previouspath!=null)
					    	           {
			    					   Expr previous=ctx.mkIntConst(previouspath);
			    					   solver.add(ctx.mkGt((ArithExpr)current, (ArithExpr)previous));
				    	        		solver.add(ctx.mkGe((ArithExpr)current, ctx.mkInt(0)));
						    	     	solver.add(ctx.mkGe((ArithExpr)previous, ctx.mkInt(0)));
					    	           } 
					    	           previouspath=currentpath;
					    	           int argcount=expr.getArgCount();
					    	           Value arrayl[]=new Value[3];
					    	           for(int count=0;count<argcount;count++)
					    	           {
					    	        	   Value arg=expr.getArg(count);
					    	        	   arrayl[count]=arg;
					    	           }
					    	          if(!expr.getMethod().toString().contains("init"))
					    	          {
					    	        	  if(expr instanceof VirtualInvokeExpr)
					    	        	  {
						    	           String subsig=newmethod.getSubSignature();
						    	          String e=((VirtualInvokeExpr)expr).getBase().getType().toString();
						    	          SootMethod method2 = Scene.v().getMethod("<"+e+": "+subsig+">");
						    	          System.out.println(method2);
						    	          newmethod=method2;
					    	        	  }
					    	          }
					    	          traversemethod(tid,newmethod,arrayl);
			    					   
			    					   System.out.println("previous path is :"+previouspath);
			    					//   solver.add(ctx.mkGt((ArithExpr)next, (ArithExpr)current));
			    					   }
			    					   }
			    				   }
			    				 
			    				   }
			    				   
			    			   }   // if(stmt instanceof InvokeStmt)   ends
			    		  
			    		  
			    	   }        //while(stmtIt.hasNext()) ends
			    	   
			    	  }       //   if(blockid==block.getIndexInMethod()) ends
			    	   
			      }       //for(Block block:cfg.getBlocks()) ends
			   
			      
			      i++;
		      }   // while(i<blockids.length) ends
	      
	      

        	}
	protected String Returnobject(String str)
	{
		String[] str1=str.split(" ");
		String str2=str1[str1.length-1];
		str2=str2.substring(0, str2.length()-1);
		return(str2);
	}
	protected boolean isLockStmt(String str)
	{
		String[] str1=str.split(" ");
		return(str1[str1.length-2].equals("java.util.concurrent.locks.Lock"));
	}
	
	protected void addlaststmtofthread(String tid)
	{
		for(SootClass class2:Scene.v().getApplicationClasses())
		{
			
			for(SootMethod method:class2.getMethods())
			{
				if(!method.getSignature().contains("popUtil.PoP_Util"))
				{
			//	System.out.println("minimum in the outer for loop");
				if((tid.equals("0") && method.getSignature().toString().equals("void main(java.lang.String[])")) || (!(tid.equals("0")) && method.getSignature().toString().equals("void run()")))
				{
	
					String tuplekey=method.getSignature()+","+tid;
				//	System.out.println("tuple key is :"+tuplekey);
					String tuple=map1.get(tuplekey);
					ExceptionalBlockGraph cfg=new ExceptionalBlockGraph(method.getActiveBody());
					String previouspath=null;
					String currentpath=null;
					int stmtno1=0;
				//	System.out.println(tuple);
					String[] tuplefields=tuple.split(",");
				 	String[] blockids=tuplefields[3].split("->"); 
		 		    int i=0;
				    int blockid;
			        while(i<blockids.length)
				      {
					      blockid=Integer.parseInt(blockids[i]);
					      for(Block block:cfg.getBlocks())
					      {
					    	  if(blockid==block.getIndexInMethod())
					    	  {
					    	   Body bodyofblock=block.getBody();
					    	   Chain units=(Chain) bodyofblock.getUnits();
					    	   Unit head=block.getHead();
					    	   Unit tail=block.getTail();
					    	   Iterator stmtIt = units.iterator(block.getHead(),block.getTail());
					    	   while(stmtIt.hasNext())
					    	   {					    		   					    		 
					    		   Stmt stmt=(Stmt) stmtIt.next();
					    		  if(stmt instanceof AssignStmt)
					    		  {
					    			Value leftop=((AssignStmt) stmt).getLeftOp();
					    			Value rightop=((AssignStmt) stmt).getRightOp();
					    			String type1=leftop.getType().toString();
					    			boolean check1=type1.equals("java.lang.Integer") || type1.equals("java.lang.Character") || type1.equals("java.lang.Boolean")
					    					|| type1.equals("java.lang.Float") || type1.equals("java.lang.Double") || type1.equals("java.lang.Long");
					    			String type2=rightop.getType().toString();
					    			boolean check2=type2.equals("java.lang.Integer") || type2.equals("java.lang.Character") || type2.equals("java.lang.Boolean")
					    					|| type2.equals("java.lang.Float") || type2.equals("java.lang.Double") || type2.equals("java.lang.Long");
					    			
					    			if((leftop instanceof StaticFieldRef && check1)|| (rightop instanceof StaticFieldRef && check2))
					    			{
					    				
					    				stmtno1++;
					    			}
					    		  }
					    		  if(stmt instanceof InvokeStmt)
					    		  {
					    			  if(stmt.toString().endsWith("void start()>()") || stmt.toString().endsWith("void join()>()") || stmt.toString().endsWith("void lock()>()")
					    					   || stmt.toString().endsWith("void unlock()>()"))
					    			  {
					    				  stmtno1++;
					    			  }
					    		  }

					    		  if(stmt instanceof ReturnStmt || stmt instanceof ReturnVoidStmt)
					    		  {

					    			  currentpath="O_"+tid+"_"+tuplefields[2]+"_";
					    				stmtno1++;
					    				currentpath=currentpath.concat(""+stmtno1);	
					    				
					    				laststmtofthread.put(tid, currentpath);
					    		  }					    
					    		}
					    	  }
					      }
					      i++;
				      }
				}
				}
								
			}
		}
	}
	
	protected void Addlockunlockconstraints()
	{
		Set keys=lockmap.keySet();
		Set keys2=unlockmap.keySet();
		Iterator i=keys.iterator();
		System.out.println(lockmap);
		System.out.println(unlockmap);
		while(i.hasNext())
		{
			String lock=(String) i.next();
			List<String> ordervars=lockmap.get(lock);
			Iterator listofvars=ordervars.listIterator();
					while(listofvars.hasNext())
					{
						String lockOvar=(String) listofvars.next();
						String[] ordervariablestr=lockOvar.split("_");
						String tid=ordervariablestr[1];
						
						Iterator j=keys2.iterator();
						String unlockOvar=null;
						
						while(j.hasNext())
						{
							String unlock=(String) j.next();
							if(lock.equals(unlock))
							{
								List<String> unordervars=unlockmap.get(unlock);
								Iterator listofunvars=unordervars.listIterator();
								while(listofunvars.hasNext())
								{
									String unordervariable=(String) listofunvars.next();
									String[] unordervariablestr=unordervariable.split("_");
									String threadid=unordervariablestr[1];
									if(tid.equals(threadid))
									{
										unlockOvar=unordervariable;
									}
								}
							}
						}
						//System.out.println("Lock variable : "+lockOvar+" And unlock variable isi : "+ unlockOvar);
						Set keys3=lockmap.keySet();
						Set keys4=unlockmap.keySet();
						Iterator k=keys.iterator();
						while(k.hasNext())
						{
							String lock1=(String) k.next();
							if(lock.equals(lock1))
							{
							List<String> ordervars1=lockmap.get(lock1);
							Iterator listofvars1=ordervars1.listIterator();
							while(listofvars1.hasNext())
							{
								String lockOvar1=(String) listofvars1.next();
								String[] ordervariablestr1=lockOvar1.split("_");
								String tid1=ordervariablestr1[1];
								if(!tid.equals(tid1))
								{
								Iterator l=keys4.iterator();
								String unlockOvar1=null;
								while(l.hasNext())
								{
									String unlock1=(String) l.next();
									if(lock1.equals(unlock1))
									{
										List<String> unordervars1=unlockmap.get(unlock1);
										Iterator listofunvars1=unordervars1.listIterator();
										while(listofunvars1.hasNext())
										{
											String unordervariable1=(String) listofunvars1.next();
											String[] unordervariablestr1=unordervariable1.split("_");
											String threadid1=unordervariablestr1[1];
											if(tid1.equals(threadid1))
											{
												unlockOvar1=unordervariable1;
											}
										}
									}
								}
								if(!lockOvar.equals(lockOvar1))
								{
									Expr exp1=ctx.mkIntConst(lockOvar);
									Expr exp2=ctx.mkIntConst(unlockOvar);
									Expr exp3=ctx.mkIntConst(lockOvar1);
									Expr exp4=ctx.mkIntConst(unlockOvar1);
									solver.add(ctx.mkGt((ArithExpr)exp2, (ArithExpr)exp1));
									solver.add(ctx.mkGt((ArithExpr)exp4, (ArithExpr)exp3));
									solver.add(ctx.mkOr(ctx.mkGt((ArithExpr)exp1, (ArithExpr)exp4),ctx.mkGt((ArithExpr)exp3,(ArithExpr) exp2)));
						//			solver.add(ctx.mkGe((ArithExpr)exp1, ctx.mkInt(0)));
					    	  //   	solver.add(ctx.mkGe((ArithExpr)exp2, ctx.mkInt(0)));
					    	 //   	solver.add(ctx.mkGe((ArithExpr)exp3, ctx.mkInt(0)));
					    	//     	solver.add(ctx.mkGe((ArithExpr)exp4, ctx.mkInt(0)));
								}
								//System.out.println("For every lock: "+lockOvar+"same locks n unlocks in other threads: "+lockOvar1+"  "+unlockOvar1);
								}
								}
							}
						}
						
					}

		}
	}
	
	protected void ifConstraints(Value condition,Boolean state,String tid)
	{
	
		  BinopExpr expr=(BinopExpr) condition;
		  Value op1=expr.getOp1();
		  Value op2=expr.getOp2();
		  String operator=expr.getSymbol();
		  ConditionExpr cond=(ConditionExpr) condition;
		  String op=cond.getSymbol().toString();
		  if(op1 instanceof Local && op2 instanceof Constant)
		  {
			  int secondop=Integer.parseInt(op2.toString());
			  String symb_name_local=getSymbNameLocalRead(op1.toString(),tid);
			  Expr firstop=ctx.mkIntConst(symb_name_local);
			  Expr secondopex=ctx.mkNumeral(secondop,ctx.mkIntSort());
			 if(state)
			 {
			  if((expr instanceof NeExpr))
			  {
				  solver.add((ctx.mkEq(firstop, secondopex)));
				  System.out.println("expresion is not equal and ");
			  }
			  else if(expr instanceof EqExpr)
			  {
				  solver.add(ctx.mkNot(ctx.mkEq(firstop, secondopex)));
			  }
			  else if(expr instanceof GtExpr)  
			  {
				  solver.add(ctx.mkLe((ArithExpr)firstop,(ArithExpr)secondopex));
			  }
			  else if(expr instanceof GeExpr)  
			  {
				  solver.add(ctx.mkLt((ArithExpr)firstop,(ArithExpr)secondopex));
			  }
			  else if(expr instanceof LtExpr)  
			  {
				  solver.add(ctx.mkGe((ArithExpr)firstop,(ArithExpr)secondopex));
			  }
			  else if(expr instanceof LeExpr)  
			  {
				  solver.add(ctx.mkGt((ArithExpr)firstop,(ArithExpr)secondopex));
			  }
		     }
			 else
			 {
				 if(expr instanceof NeExpr)
					 solver.add(ctx.mkNot(ctx.mkEq(firstop, secondopex)));
				 else if(expr instanceof EqExpr)
					 solver.add((ctx.mkEq(firstop, secondopex)));
				 else if(expr instanceof GtExpr)
					 solver.add(ctx.mkGt((ArithExpr)firstop, (ArithExpr)secondopex));
				 else if(expr instanceof GeExpr)
					 solver.add(ctx.mkGe((ArithExpr)firstop, (ArithExpr)secondopex));
				 else if(expr instanceof LtExpr)
					 solver.add(ctx.mkLt((ArithExpr)firstop, (ArithExpr)secondopex));
				 else if(expr instanceof LeExpr)
					 solver.add(ctx.mkLe((ArithExpr)firstop, (ArithExpr)secondopex));
			 }
			 
		  }
	}
	protected String getSymbNameLocal(String local,String tid)
	{
		int version=localfieldsmap.get(local+"_"+tid);
	
		version=version+1;
		
		localfieldsmap.put(local+"_"+tid, version);
		
		String symb_name_local=local+"_"+tid+"_"+version;
		return symb_name_local;
	}
	protected String getSymbNameLocalRead(String local,String tid)
	{
		int version=localfieldsmap.get(local+"_"+tid);	
		String symb_name_local=local+"_"+tid+"_"+version;
		return symb_name_local;
	}
	protected void  AddReadWriteConstraints()              // best luck
	{
		SootMethod meth1,meth2;
		while(!allthreads.isEmpty())
		{
			String tid=allthreads.remove();
	
		
	    	if(tid.equals("0"))
	    	{
	    		for(SootClass class1:Scene.v().getApplicationClasses())
	    		{
	    			for(SootMethod method:class1.getMethods())
	    			{
	    				if(method.getSignature().toString().contains("void main(java.lang.String[])"))
	    				{
	    					m=method;
	    					
	    				}
	    				if(method.getSignature().toString().contains("clinit"))
	    				{
	    				if(method.getSignature().startsWith("<test"))
	    				{
	    					meth=method;
	    				}
	    				}
	    			}
	    		}
	    		ReadWriteConstraints(meth,tid);
	    		ReadWriteConstraints(m,tid);
	    	}
	    	else
	    	{
	    		for(SootClass class1:Scene.v().getApplicationClasses())
	    		{
	    			for(SootMethod method:class1.getMethods())
	    			{
	    				if(method.getSignature().toString().contains("void run()"))
	    				{
	    					m=method;
	    				}
	    			}
	    		}
	    		ReadWriteConstraints(m,tid);
	    	}
		}
	}
	protected void ReadWriteConstraints(SootMethod method,String tid)
	{
		
		System.out.println("threadid is:"+tid+"and method os :"+method.getSignature());
		String tuplekey=method.getSignature()+","+tid;
		//	System.out.println("tuple key is :"+tuplekey);
			String tuple=map1.get(tuplekey);
			ExceptionalBlockGraph cfg=new ExceptionalBlockGraph(method.getActiveBody());
			String previouspath=null;
			String currentpath=null;
			int stmtno1=0;
		//	System.out.println(tuple);
			String[] tuplefields=tuple.split(",");
		 	String[] blockids=tuplefields[3].split("->"); 
 		    int i=0;
		    int blockid;
		    while(i<blockids.length)
		      {
			      blockid=Integer.parseInt(blockids[i]);
			      for(Block block:cfg.getBlocks())
			      {
			    	  if(blockid==block.getIndexInMethod())
			    	  {
			    	   Body bodyofblock=block.getBody();
			    	   Chain units=(Chain) bodyofblock.getUnits();
			    	   Unit head=block.getHead();
			    	   Unit tail=block.getTail();
			    	   Iterator stmtIt = units.iterator(block.getHead(),block.getTail());
			    	   while(stmtIt.hasNext())
			    	   {					    		   					    		 
			    		   Stmt stmt=(Stmt) stmtIt.next();
			    		  if(stmt instanceof AssignStmt)
			    		  {
			    			Value leftop=((AssignStmt) stmt).getLeftOp();
			    			Value rightop=((AssignStmt) stmt).getRightOp();
			    			String type=rightop.getType().toString();
			    			boolean check=type.equals("java.lang.Integer") || type.equals("java.lang.Character") || type.equals("java.lang.Boolean")
			    					|| type.equals("java.lang.Float") || type.equals("java.lang.Double") || type.equals("java.lang.Long");
			    			String type1=leftop.getType().toString();
			    			boolean check1=type1.equals("java.lang.Integer") || type1.equals("java.lang.Character") || type1.equals("java.lang.Boolean")
			    					|| type1.equals("java.lang.Float") || type1.equals("java.lang.Double") || type1.equals("java.lang.Long");
			    			
			    			//System.out.println(leftop instanceof StaticFieldRef);
			    			if(leftop instanceof StaticFieldRef && check1)
			    			{
			    				
			    				//	System.out.println(tid+":...:"+leftop);
			    				if(symbTableforRW.containsKey(leftop.toString()))
			    				{
			    			
			    					int version = symbTableforRW.get(leftop.toString());
			    					version++;
			    					symbTableforRW.put(leftop.toString(), version);
			    				}
			    				else
			    				{
			    					//System.out.println("Adding : "+leftop.toString()+"to table");
			    					symbTableforRW.put(leftop.toString(), 1);
			    				}
			    			}
			    			if(rightop instanceof StaticFieldRef && check)
			    			{
			    			//	System.out.println("right op is :"+rightop);
			    				int ver=symbTableforRW.get(rightop.toString());
			    			String var_name=Returnobject(rightop.toString());
			    			ver++;
			    			symbTableforRW.put(rightop.toString(), ver);
			    			String symbname=var_name+"_"+ver;
			    			HashMap<String,String> allwrites=new HashMap<>();
			    			allwrites=writestatic.get(var_name);
			    			List<Expr> constraints=new ArrayList<>();
			    			//System.out.println(symbname);
			    			Expr exp=ctx.mkBool(false);
			    			for(String str:allwrites.keySet())
			    			{
			    				String OVarW=allwrites.get(str);
			    				String OVarR=StaticReadOVar.get(symbname);
			    				List<Expr> constrinside=new ArrayList<>();
			    				Expr exp1=null;
			    				exp1=ctx.mkAnd(ctx.mkEq(ctx.mkIntConst(symbname), ctx.mkIntConst(str)),ctx.mkGt(ctx.mkIntConst(OVarR), ctx.mkIntConst(OVarW)));
			    				for(String othersymbvar:allwrites.keySet())
			    				{
			    					
			    					String OVarW2=allwrites.get(othersymbvar);
			    					if(!othersymbvar.equals(str))
			    					{
			    						exp1=ctx.mkAnd((BoolExpr)exp1,ctx.mkOr(ctx.mkGt(ctx.mkIntConst(OVarW2), ctx.mkIntConst(OVarR)),ctx.mkGt(ctx.mkIntConst(OVarW), ctx.mkIntConst(OVarW2))));
			    				
			    					}
			    				}
			    				exp=ctx.mkOr((BoolExpr)exp1,(BoolExpr)exp);
			    			}
			    			solver.add((BoolExpr)exp);
			    			//System.out.println(allwrites);
			    			}
			    		  }
			    	   }
			    	  }
			      }
			      i++;
		      }
		    System.out.println("end of readwrite");
	}
	protected void ReadWrite2()
	{
		for(String Rvar:readstatic.keySet())
		{
			HashMap<String,String> Rmap=new HashMap<>();
			Rmap=readstatic.get(Rvar);
			HashMap<String,String> Wmap=new HashMap<>();
			Wmap=writestatic.get(Rvar);
			
			for(String Rsymb:Rmap.keySet())
			{
				Expr exp=null;
				String Rsymbovar=Rmap.get(Rsymb);
				for(String Wsymb:Wmap.keySet())
				{
					String Wsymbovar=Wmap.get(Wsymb);
					Expr exp1=null;
					exp1=ctx.mkAnd(ctx.mkEq(ctx.mkIntConst(Rsymb),ctx.mkIntConst(Wsymb)),ctx.mkGt(ctx.mkIntConst(Rsymbovar), ctx.mkIntConst(Wsymbovar)));
					for(String otherWSymb:Wmap.keySet())
					{
						if(!Wsymb.equals(otherWSymb))
						{
							String otherWSymbovar=Wmap.get(otherWSymb);
							exp1=ctx.mkAnd((BoolExpr)exp1,ctx.mkOr(ctx.mkGt(ctx.mkIntConst(otherWSymbovar), ctx.mkIntConst(Rsymbovar)),ctx.mkGt(ctx.mkIntConst(Wsymbovar), ctx.mkIntConst(otherWSymbovar))));
						}
					}
					if(exp!=null)
					exp=ctx.mkOr((BoolExpr)exp1,(BoolExpr)exp);
					else
						exp=exp1;
					
					//System.out.println(Rsymb+Rsymbovar+Wsymb+Wsymbovar);
					
				}
				solver.add((BoolExpr)exp);
			}
		}
	}
	protected void lockunlockconstraints()
	{
		for(String lockname:locksmap2.keySet())
		{
			List<String> listoflocks=locksmap2.get(lockname);
			Iterator itr = listoflocks.iterator();
			
			while(itr.hasNext())
			{
				
				String lockunlock=(String) itr.next();
				String[] lockunlockvars=lockunlock.split("#");
				String lock1=lockunlockvars[0];
				String unlock1=lockunlockvars[1];
				String[] lock1data=lock1.split("_");
				String tid1=lock1data[1];
				Iterator itr2=listoflocks.iterator();
				//System.out.println(lockname+lockunlock);	
				while(itr2.hasNext())
				{
					
					String lockunlock2=(String) itr2.next();
					String[] lockunlockvars2=lockunlock2.split("#");
					String lock2=lockunlockvars2[0];
					String unlock2=lockunlockvars2[1];
					String[] lock2data=lock2.split("_");
					String tid2=lock2data[1];
					if(!tid1.equals(tid2))
					{
					//	System.out.println(lock1+":"+unlock1+","+lock2+":"+unlock2);
						solver.add(ctx.mkOr(ctx.mkGt(ctx.mkIntConst(lock1), ctx.mkIntConst(unlock2)),ctx.mkGt(ctx.mkIntConst(lock2), ctx.mkIntConst(unlock1))));
					}
				}
				
			}
		}
	}
}
