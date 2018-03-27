// package e0210;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;



public class MyClass {
//private static HashMap<Long,String> map=new HashMap<>();
//private static HashMap<Long,Integer> map2=new HashMap<>();
	private static String arr[]=new String[10000];
	private static int arrnum[]=new int[10000];
	private static HashMap[] hs=new HashMap[10000];
	
    //private static HashMap<String, HashMap<String,Integer>> outer=new HashMap<String, HashMap<String,Integer>>();
public static synchronized void add(long childthreadId)
{
	long parentthreadId=Thread.currentThread().getId();
	String tid=arr[(int) parentthreadId];
	int numberofthreads=arrnum[(int) parentthreadId];
	String childtid=tid + "." + numberofthreads;
//	System.out.println("new child thread id is :"+childtid);
	numberofthreads++;
	arrnum[(int) parentthreadId]=numberofthreads;

	arr[(int) childthreadId]=childtid;
}

public static synchronized void add2(String e)
{
	long threadId=Thread.currentThread().getId();
	arr[(int) threadId]="0";
	arrnum[(int) threadId]=0;
	//map.put(threadId, "1");
	//map2.put(threadId, 0);
	
}


public static synchronized void print22(String str,int n,String pathid)
{
	long threadId=Thread.currentThread().getId();
//	String str=map.get(threadId);
//	System.out.print(str + ",");
	//System.out.println("current thread id is"+threadId);

	   int num;
	  if(hs[(int)threadId]==null)
	  {
		  hs[(int) threadId]=new HashMap();
	  }
	  HashMap map=hs[(int) threadId];
	  
	  if(map.containsKey(str))
	  {
		  num=(int) map.get(str);
		  num++;
		  //System.out.println(num+","+n);
		
		  map.put(str, num);
	  }
	  else
	  {
		  map.put(str, 0);
		 num=0;
		  // System.out.println(0+","+n);
	  }
	// System.out.println("threadid is : "+arr[(int)threadId]);
		System.out.println(str+","+arr[(int) threadId]+","+num+","+pathid+"&" + n);
 
}
public static synchronized String concatinate(String current,int ballid)
{
	String str;
	if(current.equals(""))
	{
		//System.out.println("yeah came in this");
		str="&"+String.valueOf(ballid);
	}
	else
	 str=current + "&" + String.valueOf(ballid);
	return str;
}

}
