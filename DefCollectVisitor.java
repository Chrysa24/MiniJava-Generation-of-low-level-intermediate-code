//package visitor;

//import MiniJavaParser;
//import java.io.FileInputStream;
import visitor.GJDepthFirst;
import syntaxtree.*;
import java.util.*;  
import java.util.Map.Entry;
import java.io.*;
import static javax.swing.UIManager.get;


public class DefCollectVisitor extends GJDepthFirst<String,String>{
    
        boolean offsetflag=false;
        boolean errorflag = false;
        int param_counter=0;
        String classname1=null, classname2=null;
        String Mainclass = null;
        HashMap<String,Integer>func_counter = new LinkedHashMap<String,Integer>();
        int fun_counter=0;
        HashMap<String,String> variables;
        HashMap<String, HashMap> scope;
        List<HashMap> list;
        List<HashMap> array_offs ;
        HashMap< String, List> offsets= new LinkedHashMap< String, List>() ;
        HashMap< String, Integer> offset_of_class;
        HashMap< String, Integer> offset_of_fun_class;
        HashMap<String,String>extend_classes = new LinkedHashMap<String,String>();
        
        HashMap<String,Integer>override_classes = new LinkedHashMap<String,Integer>();
       
        String FileName=null;
     
     public List<List> SymbolTable=new ArrayList<List>();
      
   public String visit(Goal n, String argu) {
       
     
      FileName = argu;
      String _ret=null;
      n.f0.accept(this, argu);
      n.f1.accept(this, argu);
      if (errorflag==true){
          System.out.println("ERROR");
          return null;
      }
      ListIterator<List> Tableitr=SymbolTable.listIterator();
   
      n.f2.accept(this, argu);
      if (errorflag==true){
          System.out.println("ERROR");
          return null;
      }
  
      return _ret;
   }
   
   
   public String visit(MainClass n, String argu) {
      list=new ArrayList<HashMap>();
      variables = new LinkedHashMap<String, String>();
      scope = new HashMap<String, HashMap>();
      String _ret=null;
      String main = n.f1.accept(this, argu);
      Mainclass = main;
      func_counter.put(main,0);
      String arg = n.f11.accept(this, argu);
      variables.put(arg, "String[]");
      n.f14.accept(this, "main");
      if( errorflag== true)
           return _ret;             
      scope.put(main, variables);
      list.add(scope);
      SymbolTable.add(list);
      n.f15.accept(this, argu);
      return _ret;
   }
 
   public String offset_fun( String id){
       
       ListIterator<List> Tableitr=SymbolTable.listIterator();
       ListIterator  listitr=null;
       Object extend_vars =  null;
       List next;
       int func_counter=0;
       int of_counter=0;
       
       while(Tableitr.hasNext()) {
          next = Tableitr.next();
          listitr=next.listIterator();
      
          while(listitr.hasNext()) {
          
               HashMap next_map = (HashMap)listitr.next();
               extend_vars = next_map.get(classname1);                  //klasi
             
                if(extend_vars != null && listitr.hasNext()){
                      func_counter ++;
                      while(listitr.hasNext()) {
                           if( ((HashMap)listitr.next()).get(id)!=null){     // diladi an uparxei synartisi me to idio onoma
                                                                                                    //mesa sthn idia klasi einai error stin minijava
                               errorflag = true;
                               return null;
                   
                           }
                      }
                       break;
                }
                
                extend_vars = next_map.get(classname2);             //yperklasi
                
                if(extend_vars != null && listitr.hasNext()){
                    
                      func_counter ++;
                    
                      while(listitr.hasNext()) {
                           if( ((HashMap)listitr.next()).get(id)!=null){     // diladi an uparxei synartisi me to idio onoma
                               of_counter =1;
                               break;
                   
                           }
                      }
                       break;
                }
                break;
            }
            extend_vars = null;
        }
          
       String ext_name = classname2;
       while(ext_name !=null){
      
           if( extend_classes.get(ext_name) !=null){                    //elegxoume sthn lista me ta zeygh an exei ki alli yperklasi
                ext_name = extend_classes.get(ext_name);
                        
           }
           else
                ext_name = null;
      
           Tableitr = SymbolTable.listIterator();
           while(Tableitr.hasNext() && ext_name != null) {
                next = Tableitr.next();
                listitr=next.listIterator();
                while(listitr.hasNext()) {
                       HashMap next_map = (HashMap)listitr.next();
                       extend_vars = next_map.get(ext_name);                  //klasi
                                 
                       if(extend_vars != null && listitr.hasNext()){
                                    
                             func_counter ++;
                             while(listitr.hasNext()) {
                                  if( ((HashMap)listitr.next()).get(id)!=null){     // diladi an uparxei synartisi me to idio onoma
                                      of_counter =1;
                                      break;
                                  }
                               }
                               break;
                      }
                      break;
               }
           }
                                  
      }

     
       int sum_counter = of_counter;
     
      if(override_classes.get(classname1) !=null){
           sum_counter = sum_counter+override_classes.get(classname1);
        
           override_classes.put(classname1,sum_counter);
      }
      else{
            if(override_classes.get(classname2) !=null){
                sum_counter = sum_counter+override_classes.get(classname2);

                override_classes.put(classname1,sum_counter);
            }
            else
                override_classes.put(classname1,sum_counter);
      }
  
     
      if(of_counter==0){
          offset_of_fun_class.put(id, func_counter*8 - sum_counter*8);
          fun_counter ++;
      }
  
      return null;
   }
   
   public String offset_var(HashMap vars, String id){
        
       int lastoffset =0;
        Iterator iterator = vars.entrySet().iterator();
        Map.Entry firstEntry=null, lastEntry =null;
        while(iterator.hasNext()){
            Map.Entry entry = (Map.Entry) iterator.next();
            if(firstEntry != null) {
            } else {
                firstEntry = entry;
            }
            lastEntry = entry;
        }
        if(null == firstEntry ){             //einai i 1h metabliti tis klasis-elegxoume an exei yperklasi
            
           
            if(classname2 != null && classname1 != Mainclass){         //an exei yparklasi kai den einai h main class prepei na ksekinisoume apo ekei pou meiname
               ListIterator<List> Tableitr=SymbolTable.listIterator();
               ListIterator  listitr=null;
               Object extend_vars =  null;

              
               while(Tableitr.hasNext()) {
                  List next;

                  next = Tableitr.next();
                  
                  listitr=next.listIterator();
                  while(listitr.hasNext()) {
                       HashMap next_map = (HashMap)listitr.next();

                       extend_vars = next_map.get(classname1);

                        if(extend_vars != null){                        // an i iperklasi exei fields
                           
                            iterator = ((HashMap)extend_vars).entrySet().iterator();
                            //Map.Entry var =iterator.next();
                            Map.Entry newfirstEntry=null, newlastEntry =null;
                            
                            while(iterator.hasNext()){
                                
                                Map.Entry entry = (Map.Entry) iterator.next();
                                
                                if(newfirstEntry != null) {
                                } else {
                                    newfirstEntry = entry;
                                }
                                newlastEntry = entry;
                            }
                             
                            if(newlastEntry !=null){                // briskoume tin teleutaia metabliti tis yperklasis
                              
                               
                                  lastoffset = (int)((HashMap)offsets.get(classname1).get(0)).get((String)newlastEntry.getKey());       // briskoume to offset tis
                              
                                if(newlastEntry.getValue() == "int"){
                                    offset_of_class.put( id, lastoffset+4);
                                }
                                else if(newlastEntry.getValue() == "boolean"){
                                    offset_of_class.put(  id, lastoffset+1);
                                }
                                else{
                                     offset_of_class.put(  id, lastoffset+8);
                                }
                            }
                            else
                                offset_of_class.put(id, 0);
                            return null;
                        }
                  }
               }
            
            }
            else
                 offset_of_class.put(id, 0);
            
            return null;
        }
        else{                                                   // an den einai i prwti metabliti tis klasis
            if(null == lastEntry)
                return null;
            lastoffset = offset_of_class.get((String)lastEntry.getKey());
            if(lastEntry.getValue() == "int"){
                offset_of_class.put( id, lastoffset+4);
            }
            else if(lastEntry.getValue() == "boolean"){
                offset_of_class.put(  id, lastoffset+1);
            }
            else{
                 offset_of_class.put(  id, lastoffset+8);
            }
        }
       return null;
   }
   
 
   
    public String visit(VarDeclaration n , String argu){
                          if( errorflag== true)
                            return null;      
                          
                          String _ret = null;
                          String type  =  n.f0.accept(this, argu);
                          if(type==null)
                               return _ret;
                          String id = n.f1.accept(this, argu);
                          if(variables.containsKey(id) == true)         //an h metabliti yparxei idi sto scope ayto error
                              errorflag=true;
                          
                          if( variables.containsKey(id) == true){
                              return null;
                          }
                  
                          if(offsetflag==true )
                                offset_var(variables,  id);
                    
                         variables.put(id, type);
                          return _ret;
        }
    
    public String visit(NodeToken n, String argu) { return n.toString(); }


    public String visit(BooleanArrayType n, String argu) {
        return "boolean[]";
   }
    
    public String visit(IntegerArrayType n, String argu) {
      return "int[]";
   }
    
   
   public String visit(ClassDeclaration n, String argu) {
       
       if( errorflag== true)
            return null;   
       
      list=new ArrayList<HashMap>();
      variables = new LinkedHashMap<String, String>();
      scope = new HashMap<String, HashMap>();
      offset_of_class = new LinkedHashMap<String,Integer>();
      offset_of_fun_class = new LinkedHashMap<String,Integer>();
      array_offs = new ArrayList<HashMap>();
      
      String _ret=null;
      String type = n.f1.accept(this, argu);
      
       ListIterator<List> Tableitr=SymbolTable.listIterator();
      ListIterator  listitr=null;
      Object extend_vars =  null;
     
      while(Tableitr.hasNext()) {
               
          listitr=Tableitr.next().listIterator();
           if(listitr.hasNext()){
               HashMap next_map = (HashMap)listitr.next();
               extend_vars = next_map.get(type);                  //klasi
               if(extend_vars !=null){
                   errorflag=true;
                   return _ret;
               }
           }
      }
      
      n.f2.accept(this, argu);
      offsetflag=true;
      classname1=type;
      n.f3.accept(this, type);
      offsetflag=false;
      if (errorflag==true)
          return null;
      scope.put(type, variables);
      list.add(scope);
      n.f4.accept(this, type);
      if (errorflag==true)
          return null;
      if(n.f4.present() == false)
            SymbolTable.add(list);
      classname1=null;
      array_offs.add(0,offset_of_class);
      array_offs.add(1, offset_of_fun_class);
      offsets.put(type, array_offs);
      
      func_counter.put(type,fun_counter);
      fun_counter =0;
      return _ret;
   }
   
     
   public String visit(FormalParameter n, String argu) {
      String _ret=null;
      String type = n.f0.accept(this, argu);
      String id = n.f1.accept(this, argu);
      variables.put("chrysa_arg" + argu, type);
      variables.put(id, type);
      return _ret;
   }
   
   
   public String visit(FormalParameterTerm n, String argu) {
      String _ret=null;
      
      param_counter = param_counter +1;
      n.f1.accept(this, String.valueOf(param_counter));
     
      return _ret;
   }
   
   
   public String visit(FormalParameterTail n, String argu) {
      return n.f0.accept(this, argu);
   }

   
   
   public void checkoverload(String classname, String functionname){
       
       ListIterator<List> Tableitr;
       ListIterator  listitr;
       Object extend_vars=null,fun_vars=null ;
     
      if( extend_classes.get(classname) ==null) 
          return;
      
       while( extend_classes.get(classname) !=null) {                   //elegxoume sthn lista me ta zeygh an exei ki alli yperklasi
                
                classname = extend_classes.get(classname);
                Tableitr=SymbolTable.listIterator();
                while(Tableitr.hasNext()) {

                   listitr= Tableitr.next().listIterator();

                   while(listitr.hasNext()) {

                        HashMap next_map = (HashMap)listitr.next();
                        extend_vars = next_map.get(classname);                  //klasi
                        if(extend_vars !=null){
                             while(listitr.hasNext()) {
                                 next_map = (HashMap)listitr.next();
                                 fun_vars = next_map.get(functionname);
                                 if( fun_vars !=null){                                       //vrika sinartisi me idio 
                                     if( ((HashMap)fun_vars).get("return_value") != variables.get("return_value")) {
                                          errorflag=true;
                                          return;
                                     }
                                     int arg_counter=0;
                                     while( ((HashMap)fun_vars).get("chrysa_arg" + String.valueOf(arg_counter)) !=null) {
                                         if(((HashMap)fun_vars).get("chrysa_arg" + String.valueOf(arg_counter)) != variables.get("chrysa_arg" + String.valueOf(arg_counter))){
                                              errorflag=true;
                                              return;
                                         }
                                         arg_counter ++;
                                     }
                                     if(variables.get("chrysa_arg" + String.valueOf(arg_counter)) !=null){
                                              errorflag=true;
                                              return;
                                     }
                                 }
                             }
                        }

                   }
                }
       }
       
       return;
   }
 

   public String visit(MethodDeclaration n, String argu) {
       if( errorflag== true)
           return null;
       
     // list=new ArrayList<HashMap>();
      variables = new LinkedHashMap<String, String>();
      scope = new HashMap<String, HashMap>();
      String _ret=null;
      String return_value = n.f1.accept(this, argu);
      variables.put("return_value", return_value);
      String id  = n.f2.accept(this, argu);
      
      offset_fun(id);
      if (errorflag==true)
          return null;
       n.f4.accept(this, String.valueOf(param_counter));
       
       param_counter = 0;
       checkoverload(argu, id);
      n.f7.accept(this, argu + " :: " + id);
      if (errorflag==true)
          return null;
      scope.put(id, variables);
      list.add(1, scope);
      List<HashMap> helpList = new ArrayList<HashMap>();
      helpList.addAll(list);
      SymbolTable.add(helpList);
      list.remove(scope);
      n.f8.accept(this, argu);
      n.f10.accept(this, argu);
     
      return id;
   }
   
   
  
  public String visit(ClassExtendsDeclaration n, String argu) {
     
      if( errorflag== true)
          return null;   
      ListIterator<List> Tableitr=SymbolTable.listIterator();
      ListIterator listitr;
    
      Object extend_vars =  null;
      
      list=new ArrayList<HashMap>();
      
      String ext_name =  n.f3.accept(this, argu);
      String ext_name_loop = ext_name;
      
      while(ext_name_loop !=null){                          //elegxoume an kai i yperklasi mas exei diki tis yperklasi
          HashMap<String, HashMap>   extend_scope = new HashMap<String, HashMap>();
          Tableitr=SymbolTable.listIterator();
            while(Tableitr.hasNext()) {
                  List next = Tableitr.next();
                  listitr = next.listIterator();
                      HashMap next_map = (HashMap)listitr.next();
                      
                      extend_vars = next_map.get(ext_name_loop);
                      
                      if(extend_vars != null)
                          break;
                  if(extend_vars != null)
                          break;
            }
            
            if(extend_vars == null){
                 errorflag=true;
                 return null;
            }
            extend_scope.put(ext_name_loop, (HashMap)extend_vars);
            list.add(extend_scope);
          
                        
            if( extend_classes.get(ext_name_loop) !=null){                    //elegxoume sthn lista me ta zeygh an exei ki alli yperklasi
                          
                   ext_name_loop = extend_classes.get(ext_name_loop);
                        
            }
           else
                  ext_name_loop = null;
       
      }
     
      variables = new LinkedHashMap<String, String>();
      scope = new HashMap<String, HashMap>();
      offset_of_class = new LinkedHashMap<String,Integer>();
      offset_of_fun_class = new LinkedHashMap<String,Integer>();
      array_offs = new ArrayList<HashMap>();
     
      String _ret=null;
      String name = n.f1.accept(this, argu);
      
      Tableitr=SymbolTable.listIterator();
      listitr=null;
      extend_vars =  null;
     
      while(Tableitr.hasNext()) {
               
          listitr=Tableitr.next().listIterator();
           if(listitr.hasNext()){
               HashMap next_map = (HashMap)listitr.next();
               
               extend_vars = next_map.get(name);                  //klasi
               if(extend_vars !=null){
                   errorflag=true;
                   return _ret;
               }
           }
      }
      
      offsetflag=true;
      classname1=ext_name;
      classname2=name;
      n.f5.accept(this, name);
      offsetflag=false;
       if (errorflag==true)
          return null;
      scope.put(name, variables);
      list.add(0, scope);
      classname1=name;
      classname2=ext_name;
      extend_classes.put(name,ext_name);
      n.f6.accept(this, name);
      if (errorflag==true)
          return null;
      
      if(n.f6.present() == false)
            SymbolTable.add(list);
      classname1=null;
      classname2=null;
      array_offs.add(0,offset_of_class);
      array_offs.add(1, offset_of_fun_class);
      offsets.put(name, array_offs);
      
      ext_name_loop = ext_name;
      fun_counter = fun_counter + func_counter.get(ext_name_loop);
      func_counter.put(name,fun_counter);
      fun_counter =0;
      return _ret;
   }
   
}