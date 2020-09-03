import visitor.GJDepthFirst;
import syntaxtree.*;
import java.util.*;  
import java.io.*;
import java.util.Map.Entry;
import java.util.logging.Level;
import java.util.logging.Logger;



public class Third_Part_Visitor extends  GJDepthFirst<String,GJDepthFirst>{
    
 // boolean errorflag = false;
  String classname = null, functionname = null;
  String type1=null;
  int   length=0;
//  int[] param_counter, new_param_counter;
  String[] fun_call=null,class_call=null, prev_fun_call=null, prev_class_call=null;
  int [] param_counter =null;
  int [] new_param_counter  =null;
  int[] sum_args = null, prev_sum_args=null;
  int reg_counter=0,alloc_reg_counter=-1, first_reg=-1,sec_reg=-1, if_counter=-1, while_counter=-1,exp_res_counter=-4, oob_counter=-1,nsz_counter=-1, bool_array_reg=-1;
  boolean var_flag=false,newAlloc_flag=false;
  HashMap<String,String> method_args;
  HashMap<String,String>method_vars=null;
  String function_call_buffer[], new_function_call_buffer[];
  HashMap<String,List>VTable= new LinkedHashMap<String,List>();
  List<String[]>functionsVTable ;
  String value_flag=null;
  
public String FindType(String type){
    
    String new_type;
    if(type=="int")
           new_type="i32";
    else if(type=="int[]")
           new_type="i32*";
     else if(type=="boolean")
           new_type="i8";
      else
           new_type="i8*";
    return new_type;
}
  
public void MessageSendWrite(DefCollectVisitor visitor, String Nclass,String Nfunc){
    // Kanw bitcast sti morfi poy einai h synartisi poy thelw na kanw call
    ListIterator<List> Tableitr;
    ListIterator  listitr=null;
    Object extend_vars =  null,fun_vars=null;
    String return_value=null,type=null,arg=null;
    int counter=0;
    while(Nclass!=null){
        Tableitr = visitor.SymbolTable.listIterator();
        while(Tableitr.hasNext()) {

           listitr=Tableitr.next().listIterator();
            if(listitr.hasNext()){
         
               HashMap next_map = (HashMap)listitr.next();
               extend_vars = next_map.get(Nclass);                  //klasi
               if(extend_vars !=null){
                      HashMap func_map = (HashMap)listitr.next();
                      fun_vars = func_map.get(Nfunc);
                      if(fun_vars !=null){
                         try(FileWriter fw = new FileWriter(visitor.FileName, true); 
                         BufferedWriter bw = new BufferedWriter(fw);
                         PrintWriter out = new PrintWriter(bw)){
                             out.print("\t%_" + reg_counter+ " = bitcast i8* %_" + (reg_counter-1) + " to ");
                             
                            return_value = (String)((HashMap)fun_vars).get("return_value");     // typos epistrofis
                            type = FindType(return_value);
                            if(type=="i8")
                                type = "i1";
                            out.print(type + " (i8*");
                            
                            arg = (String)((HashMap)fun_vars).get("chrysa_arg" + counter);
                            while(arg !=null){
                                 type = FindType(arg);
                                 
                                 out.print(", " + type);
                                 counter++;
                                 arg = (String)((HashMap)fun_vars).get("chrysa_arg" + counter);     // ta orismata tis function
                            }
                            out.println(")*");
                            reg_counter++;
                          } catch (IOException e) {
                                
                          }
                         return;        // otan brw tin synartisi mou epistrefw
                      }
                }
            }
        }
        Nclass = visitor.extend_classes.get(Nclass);        // elegxw mipws i synartisis einai kapoias yperklasis
    }
}

public void VTable(FileWriter myWriter,DefCollectVisitor visitor, String Nclass,int funcs){
    List<String> list_funs = new ArrayList<String>();
    List<String[]>Functions = new ArrayList<String[]>();
    ListIterator<List> Tableitr;
    ListIterator  listitr=null, functions=null;
    Object extend_vars =  null,fun_vars=null;
    String Nfunc=null,return_value=null,type=null,arg=null,ext_class=null;
    int counter=0,num_funcs=1;
    
    //arxika skanarw tis synartiseis ths klasis kai apothikevw ta onomata se lista list_funs
    Tableitr = visitor.SymbolTable.listIterator();
        while(Tableitr.hasNext()) {
           listitr=Tableitr.next().listIterator();
           while(listitr.hasNext()) {
               HashMap next_map = (HashMap)listitr.next();
               extend_vars = next_map.get(Nclass);                  //klasi
               if(extend_vars !=null){
                        if(listitr.hasNext()){
                            HashMap func_map = (HashMap)listitr.next();
                            Set set = func_map.entrySet();
                            Iterator<HashMap> iterator = set.iterator();
                            while(iterator.hasNext())
                               Nfunc = (String)((Entry)(iterator.next())).getKey();
                            
                          fun_vars = func_map.get(Nfunc);
                          if(fun_vars !=null && (((HashMap)fun_vars).get("return_value"))!=null){
                              if(list_funs.contains(Nfunc) == true)
                                 break;
                              list_funs.add(Nfunc);
                          }
                   }
               }
               break;
           }
      }
       
        String[] From , To;
    // phgainw sthn yperklasi ths klasis an exei kai grafw to vtable tis alla an exoyn koini synartisi grafw to onoma tis ypoklasis
    ext_class = visitor.extend_classes.get(Nclass);
    if(ext_class!=null && ext_class!=visitor.Mainclass && (VTable.get(ext_class)!=null) ){
        functions = VTable.get(ext_class).listIterator();
        
        while(functions.hasNext()) {
            From = (String[])functions.next();
            To = new String[3];
            To[0] = From[0];
            if(list_funs.contains(From[2])){        // an tin synartisi tin exei kai h ypoklasi 
                    list_funs.remove(From[2]);      // svinoume apo thn lista tis ypoklasis gia na mhn thn janagrapsoume meta
                    To[1] = Nclass;                         // grafoyme to onoma tis ypoklasis
            }
            else
                To[1] = From[1];
            To[2] = From[2];
            Functions.add(To);
            try{
                 if(list_funs.isEmpty() && !(functions.hasNext()))
                           myWriter.write(To[0] + To[1] + "." + To[2] + " to i8*)\n");
                  else
                           myWriter.write(To[0] + To[1] + "." + To[2] + " to i8*),\n");
            } catch (IOException e) {
            }
        }
    }
   
    //prosthetw sto telos tis ypoloipes synartiseis ths klasis sto VTable tis
    if( Nclass !=visitor.Mainclass && list_funs.isEmpty()==false){
        Tableitr = visitor.SymbolTable.listIterator();
        while(Tableitr.hasNext()) {
           listitr=Tableitr.next().listIterator();
           while(listitr.hasNext()) {
               HashMap next_map = (HashMap)listitr.next();
               extend_vars = next_map.get(Nclass);                  //klasi
               if(extend_vars !=null){
                        if(listitr.hasNext()){
                            HashMap func_map = (HashMap)listitr.next();
                            Set set = func_map.entrySet();
                            Iterator<HashMap> iterator = set.iterator();
                            while(iterator.hasNext()){
                               Nfunc = (String)((Entry)(iterator.next())).getKey();
                            }
                          fun_vars = func_map.get(Nfunc);
                          if(fun_vars !=null){
                              if(list_funs.contains(Nfunc) == false)        //an den einai sti lista simainei oti tin exei kapoia yperklasi ara thn exoyme hdh grapsei
                                 break;
                              list_funs.remove(Nfunc);
                              To = new String[3];
                              return_value = (String)((HashMap)fun_vars).get("return_value");
                              type = FindType(return_value);
                              if(type=="i8")
                                  type = "i1";
                               To[0] = "i8* bitcast (" + type + " (i8*" ;
                               
                              arg = (String)((HashMap)fun_vars).get("chrysa_arg" + counter);
                              while(arg !=null){
                                  type = FindType(arg);
                                  To[0] = To[0] + ", " + type;
                                  counter++;
                                  arg = (String)((HashMap)fun_vars).get("chrysa_arg" + counter);
                              }
                                To[0] = To[0] + ")* @";
                                To[1] = Nclass;
                                To[2] = Nfunc;
                                try{
                                    if(list_funs.isEmpty())
                                           myWriter.write(To[0] + To[1] + "." + To[2] + " to i8*)\n");
                                    else
                                           myWriter.write(To[0] + To[1] + "." + To[2] + " to i8*),\n");
                                } catch (IOException e) {
                                }
                                Functions.add(To);
                          }
                   }
               }
               break;
           }
           counter=0;
      }
    }
    VTable.put(Nclass, Functions);
}

  public void WriteFile(DefCollectVisitor visitor){
      
      try{
            File myObj = new File(visitor.FileName);
            myObj.createNewFile();                          // dhmiourgw to arxeio mou
            
         } catch (IOException e) {
           System.out.println("An error occurred.");
           e.printStackTrace();
        }
        try {
         FileWriter myWriter = new FileWriter(visitor.FileName);
          
           visitor.func_counter.entrySet().forEach( entry -> {
               String Nclass = entry.getKey();
               int funcs = entry.getValue();
               
               try {                                                // grafw ta Vtables
                   if(funcs==0)                                 // An den exei kamia function einai keno
                        myWriter.write("@." + Nclass + "_vtable = global [" + funcs + " x i8*] []\n\n");
                   else{
                       myWriter.write("@." + Nclass + "_vtable = global [" + funcs + " x i8*] [\n");
                       VTable( myWriter,visitor,Nclass,funcs);
                       myWriter.write("] \n\n");
                   }
                } catch (IOException e) {
                  e.printStackTrace();
               }
           });
           myWriter.write("declare i8* @calloc(i32, i32)\n" +
                                     "declare i32 @printf(i8*, ...)\n" +
                                     "declare void @exit(i32)\n" +
                                     "\n" +
                                     "@_cint = constant [4 x i8] c\"%d\\0a\\00\"\n" +
                                     "@_cOOB = constant [15 x i8] c\"Out of bounds\\0a\\00\"\n" +
                                     "@_cNSZ = constant [15 x i8] c\"Negative size\\0a\\00\"\n" +
                                     "\n" +
                                     "define void @print_int(i32 %i) {\n" +
                                     "    %_str = bitcast [4 x i8]* @_cint to i8*\n" +
                                     "    call i32 (i8*, ...) @printf(i8* %_str, i32 %i)\n" +
                                     "    ret void\n" +
                                    "}\n" +
                                     "\n" +
                                     "define void @throw_oob() {\n" +
                                     "    %_str = bitcast [15 x i8]* @_cOOB to i8*\n" +
                                     "    call i32 (i8*, ...) @printf(i8* %_str)\n" +
                                     "    call void @exit(i32 1)\n" +
                                     "    ret void\n" +
                                     "}\n" +
                                     "\n" +
                                     "define void @throw_nsz() {\n" +
                                     "    %_str = bitcast [15 x i8]* @_cNSZ to i8*\n" +
                                     "    call i32 (i8*, ...) @printf(i8* %_str)\n" +
                                     "    call void @exit(i32 1)\n" +
                                     "    ret void\n" +
                                     "}\n\n\n");
           myWriter.close();
       } catch (IOException e) {
             e.printStackTrace();
        }
       
  } 
  
  
    public String visit(Goal n,GJDepthFirst argu) {
      DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      
      WriteFile(visitor1);
     
      n.f0.accept(this, argu);
      n.f1.accept(this, argu);
    
   //   PrintOffsets(visitor1);
      n.f2.accept(this, argu);
        return null;
    }
    
    public void PrintOffsets(DefCollectVisitor visitor){
                
        System.out.println(visitor.SymbolTable);
        
        visitor.offsets.entrySet().forEach( entry -> {
            ArrayList list = (ArrayList)entry.getValue();
            HashMap map0 = (HashMap)list.get(0);
            HashMap map1 = (HashMap)list.get(1);
            String Nclass = entry.getKey();
            Iterator iterator0 = map0.entrySet().iterator();
            Iterator iterator1 = map1.entrySet().iterator();
            Map.Entry entry0,entry1;
            
            while(iterator0.hasNext()){
                entry0 = (Map.Entry)iterator0.next();
                System.out.println(Nclass + "." + entry0.getKey() + ": " + entry0.getValue());
            }
            while(iterator1.hasNext()){
                entry1 = (Map.Entry)iterator1.next();
                System.out.println(Nclass + "." + entry1.getKey() + ": " + entry1.getValue());
            }
            
        });
    }
    
   
   public String visit(MainClass n, GJDepthFirst argu) {
       DefCollectVisitor visitor = (DefCollectVisitor)argu;
      String _ret=null;
      classname =  n.f1.accept(this, argu);
       try(FileWriter fw = new FileWriter(visitor.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw))
        {
            out.println("define i32 @main() {\n");
        } catch (IOException e) {
        }   
        
      n.f11.accept(this, argu);
      var_flag=true;
      n.f14.accept(this, argu);
      var_flag=false;
      
      n.f15.accept(this, argu);
    
      classname = null;
      try(FileWriter fw = new FileWriter(visitor.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw))
        {
      out.println("\tret i32 0");
      out.println("}\n\n");
      } catch (IOException e) {
            //exception handling left as an exercise for the reader
        }
      return _ret;
   }
    
   
   public String visit(ClassDeclaration n, GJDepthFirst argu) {
     
      String _ret=null;
      String a = n.f0.accept(this, argu);
      String id = n.f1.accept(this, argu);
      classname = id;
      var_flag=false;
      n.f3.accept(this, argu);
      n.f4.accept(this, argu);
      classname = null;
      return _ret;
   }
   
   public String visit(ClassExtendsDeclaration n, GJDepthFirst argu) {
      String _ret=null;
      String name = n.f1.accept(this, argu);
      classname = name;
      n.f3.accept(this, argu);
      var_flag=false;
      n.f5.accept(this, argu);
      n.f6.accept(this, argu);
      classname = null;
      return _ret;
   }
    
   public String visit(MethodDeclaration n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
       var_flag=true;
       reg_counter=0;
      
      String _ret=null;
     method_args = new LinkedHashMap<String, String>();
     method_vars=null;
      String return_type = n.f1.accept(this, argu);
      String name = n.f2.accept(this, argu);
      functionname = name;
      
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String ret_type = FindType(return_type);
          if(ret_type=="i8")
              ret_type = "i1";
          out.print("define " + ret_type + " @" + classname + "." + functionname + "(i8* %this");
        } catch (IOException e) {
        } 
                  
      n.f4.accept(this, argu);
     
      try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          out.print("){\n");
          for (Map.Entry mapElement : method_args.entrySet()) { 
            String key = (String)mapElement.getKey(); 
            String value = (String)mapElement.getValue();
            out.println("\t%" + key + " = alloca " + value );
            out.println("\tstore "+ value + " %."+ key + ", " + value + "* %" + key );
          
          }
        } catch (IOException e) {
        }
      
      method_vars = new LinkedHashMap<String,String>();         // edw tha apothikeytoyn oi metablites poy dhlwnontai sto
      n.f7.accept(this, argu);                                                          // eswteriko ths synartisis
      n.f8.accept(this, argu);
    
      first_reg = sec_reg = -1;
      bool_array_reg = -1;
      value_flag = "right";
      newAlloc_flag = false;
      String return_expr = n.f10.accept(this, argu);
      
            
      try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          if(type1 == "int"){    //return_type
              try { 
                  Integer.parseInt(return_expr);
                  out.println("\tret i32 "  + return_expr);
             }
             catch (NumberFormatException e)
             {
                    Nclass = Var_of_Function(visitor1,return_expr,"int");
                    if(Nclass==null){       // o typos epistrofis einai pedio ths synarthshs
                        out.println("\t%_" + reg_counter + " = load i32, i32* %"  + return_expr);
                        out.println("\tret i32 %_"  + reg_counter);
                        reg_counter++;
                    }
                    else{
                        if(return_expr==null){
                            out.println("\tret i32 %_" + (reg_counter-1));
                        }
                        else{
                            map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                            while(map.get(return_expr)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                            }
                            offset = (int)map.get(return_expr) +8;
                            out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                            reg_counter++;
                            out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                            reg_counter++;
                            out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                            out.println("\tret i32 %_" + reg_counter);
                            reg_counter++;
                        }
                      
                    }
              }
          }
          else if(type1=="boolean"){
              if(return_expr=="true" || return_expr=="false")
                  out.println("\tret i1 "  + return_expr);
              else{
                    Nclass = Var_of_Function(visitor1,return_expr,"boolean");
                    if(Nclass==null){       // o typos epistrofis einai pedio ths synarthshs
                        out.println("\t%_" + reg_counter + " = load i8, i8* %"  + return_expr);
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                        out.println("\tret i1 %_"  + reg_counter);
                        reg_counter++;
                    }
                    else{
                        if(return_expr ==null){
                            out.println("\tret i1 %_" + (reg_counter-1));
                        }
                        else{
                            map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                            while(map.get(return_expr)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                            }
                            offset = (int)map.get(return_expr) +8;
                            out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                            reg_counter++;
                            out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));
                            reg_counter++;
                            out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                            out.println("\tret i1 %_" + reg_counter);
                            reg_counter++;
                        }
                    }
                   
              }
          }
          else if(type1=="int[]"){
                    Nclass = Var_of_Function(visitor1,return_expr,"int[]");
                    if(Nclass==null){       // o typos epistrofis einai pedio ths synarthshs
                        out.println("\t%_" + reg_counter + " = load i32*, i32** %"  + return_expr);
                        out.println("\tret i32* %_"  + reg_counter);
                        reg_counter++;
                    }
                    else{
                        if(return_expr==null){
                            out.println("\tret i32* %_" + (reg_counter-1));
                        }
                        else{
                            map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                            while(map.get(return_expr)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                            }
                            offset = (int)map.get(return_expr) +8;
                            out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                            reg_counter++;
                            out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32**");      //de kserwwwwwwwwwwwwwwwwwww
                            reg_counter++;
                            out.println("\t%_" + reg_counter + " = load i32*, i32** %_" + (reg_counter-1));
                        //    out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                            out.println("\tret i32* %_" + reg_counter);
                            reg_counter++;
                        }
                      
                    }
          }
          else if(type1=="boolean[]"){
                    Nclass = Var_of_Function(visitor1,return_expr,"boolean[]");
                    if(Nclass==null){       // o typos epistrofis einai pedio ths synarthshs
                        out.println("\t%_" + reg_counter + " = load i8*, i8** %"  + return_expr);
                        out.println("\tret i8*%_"  + reg_counter);
                        bool_array_reg = reg_counter;
                        reg_counter++;
                    }
                    else{
                        if(return_expr ==null){
                            if(bool_array_reg!=-1){
                                out.println("\tret i8* %_" + bool_array_reg);
                            }
                            else{
                                out.println("\tret i8* %_" + (reg_counter-1));
                                bool_array_reg = reg_counter-1;
                            }
                        }
                        else{
                            map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                            while(map.get(return_expr)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                            }
                            offset = (int)map.get(return_expr) +8;
                            out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                            out.println("\tret i8* %_" + reg_counter);
                            bool_array_reg = reg_counter;
                            reg_counter++;
                        }
                    }
          }
          else{
                       
                       if (newAlloc_flag==true)
                            out.println("\tret i8* %_" + (reg_counter-3));
                       else if(return_expr==classname){       //this
                            out.println("\ret i8* %this");
                       }
                        else{
                            Nclass = Var_of_Function(visitor1,return_expr,type1);          //currentclass is the class thas has as field the expr
                            if(Nclass == null){ //an to expr ths synartisis
                                out.println("\t%_" + reg_counter + " = load i8*, i8** %" + return_expr);  
                                out.println("\tret i8*%_"  + reg_counter);
                                reg_counter++;
                            }
                            else{   //an to expr den einai ths synartisis
                                if(return_expr==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                                    out.println("\tret i8* %_" + (reg_counter-1));
                                }
                                else{
                                    map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                                    while(map.get(return_expr)==null){
                                        Nclass = visitor1.extend_classes.get(Nclass);
                                        map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                                    }
                                    offset = (int)map.get(return_expr) +8;
                                    out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i8**");      
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load i8*, i8** %_" + (reg_counter-1));
                                    out.println("\tret i8* %_" + reg_counter);
                                    reg_counter++;
                                }
                            }
                        }
                        newAlloc_flag=false;
          }
          
          out.print("}\n\n");
        } catch (IOException e) {
        }
      
      if(type1 != return_type){
           String cur_classname = type1;
           
           while((cur_classname = visitor1.extend_classes.get(cur_classname)) !=null){
                       if(cur_classname == return_type)
                           return _ret;
           }
         
      }
      functionname = null;
      var_flag=false;
      first_reg = sec_reg = -1;
      method_vars=null;
      return _ret;
   }
   
   
   public String visit(NodeToken n, GJDepthFirst argu) { return n.toString(); }

    
    public void Typecheck(String type,GJDepthFirst argu){
      
        DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
        if("int".equals(type) || "boolean".equals(type) ||  "int[]".equals(type) ||   "boolean[]".equals(type) ||   "class".equals(type) ||   "function".equals(type))
            return;
        else{
             ListIterator<List> Tableitr=visitor1.SymbolTable.listIterator();
            ListIterator  listitr=null;
            Object extend_vars =  null;
         
            while(Tableitr.hasNext()) {
               
               listitr=Tableitr.next().listIterator();
               while(listitr.hasNext()) {

                    HashMap next_map = (HashMap)listitr.next();
                    extend_vars = next_map.get(type);                  //klasi
                    if(extend_vars !=null){
                        type1="class";
                        return;
                    }
               }
            }
          
            return;
        }
    }
    
    
   public String visit(VarDeclaration n, GJDepthFirst argu) {
     
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      String type = n.f0.accept(this, argu);
      Typecheck(type, argu);
    
      String id = n.f1.accept(this, argu);
      if(var_flag==true){
        try(FileWriter fw = new FileWriter(visitor1.FileName, true);
             BufferedWriter bw = new BufferedWriter(fw);
             PrintWriter out = new PrintWriter(bw))
         {
             out.println("\t%" +id + " = alloca " + FindType(type) );
         }catch (IOException e) {
             //exception handling left as an exercise for the reader
         }
      }
      if(method_vars!=null)
          method_vars.put(id, type);
      return _ret;
   }
   
   
   public String visit(FormalParameter n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      String type =n.f0.accept(this, argu);
      Typecheck(type, argu);
     
      String id = n.f1.accept(this, argu);
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw))
        {
            out.print(", " + FindType(type) + " %." + id);
        }catch (IOException e) {
        }
      method_args.put(id,FindType(type));
      return _ret;
   }
   
    
   
   public String visit(IntegerLiteral n, GJDepthFirst argu) {
      
      type1 = "int";
      return n.f0.accept(this, argu);
   }
   
   
  
   public String visit(Identifier n, GJDepthFirst argu) {
       
       String cur_classname;
     
       cur_classname= classname;
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String id = n.f0.accept(this, argu);
   
      ListIterator<List> Tableitr=visitor1.SymbolTable.listIterator();
      ListIterator  listitr=null;
      Object extend_vars =  null, fun_vars=null;
      if(id ==null)
          return null;
      
      while(Tableitr.hasNext()) {
          listitr=Tableitr.next().listIterator();
           while(listitr.hasNext()) {
               
               HashMap next_map = (HashMap)listitr.next();
               if(cur_classname == null && (next_map.get(id) !=null)){
                       type1 = id;
                    return id;
               }
               extend_vars = next_map.get(cur_classname);                  //klasi
               if(cur_classname != null && extend_vars != null){
                    if(cur_classname == visitor1.Mainclass ){
                         if(extend_vars !=null && ((HashMap)extend_vars).get(id)!=null){
                             type1 = (String)((HashMap)extend_vars).get(id);
                             return id;
                         }
                    }
                    else {
                             
                       
                             if (functionname !=null){
                                 boolean flag=false;
                                 String type_flag=null;
                                 if(((HashMap)extend_vars).get(id) !=null){         //metabliti pou einai field tis klasis sthn opoia anikei h function
                                     
                                     flag=true;
                                     type_flag = (String)((HashMap)extend_vars).get(id);
                                 }
                                  ListIterator<List> Tableitr2=visitor1.SymbolTable.listIterator();
                                  while(Tableitr2.hasNext()) {
         
                                        listitr=Tableitr2.next().listIterator();
                                       while(listitr.hasNext()) {

                                          next_map = (HashMap)listitr.next();
                                   
                                          fun_vars = next_map.get(functionname);
                              
                                          if(fun_vars != null &&  ((HashMap)fun_vars).get(id) !=null){                //einai metabliti mias synartisis
                                      
                                              type1 = (String)((HashMap)fun_vars).get(id);
                                              return id;
                                          }
                                       }
                                  }
                                 if(flag==true){
                                     type1 = type_flag;
                                     return id;
                                 }
                             }
                             else if(functionname == null &&  ((HashMap)extend_vars).get(id) !=null){            //einai field tis klasis
                                     type1 = (String)((HashMap)extend_vars).get(id);
                                     return id;
                             }
                             
                    }
               }
           }
          
      }
      //mporei na einai onoma klasis
    
          
            Tableitr=visitor1.SymbolTable.listIterator();
            while(Tableitr.hasNext()) {
                listitr=Tableitr.next().listIterator();

                        HashMap next_map = (HashMap)listitr.next();
                       
                        if (next_map.get(id) != null){
                              type1 = id;
                            return id;
                          }
                         while(listitr.hasNext()){
                             next_map = (HashMap)listitr.next();
                             if (next_map.get(id) != null){
                                type1 = "function";
                                return id;
                            }
                         }
            }
                                                                                                        //den einai pedio aytis ths klasis psaxnoume gia yperklasi
           if(visitor1.extend_classes.get(cur_classname) != null){      // h klasi exei yperklasi
                                     
                while((cur_classname = visitor1.extend_classes.get(cur_classname)) !=null){
                       Tableitr=visitor1.SymbolTable.listIterator();
                       while(Tableitr.hasNext()) {
                           
                            listitr=Tableitr.next().listIterator();
                            HashMap next_map = (HashMap)listitr.next();
                            extend_vars = next_map.get(cur_classname);
                             
                            if(extend_vars !=null && ((HashMap)extend_vars).get(id)!=null){
                                type1 = (String)((HashMap)extend_vars).get(id);
                                return id;
                            }
                      }
                }
           }
          
       type1 = null;
      return id;
   }
   
   
   public String visit(CompareExpression n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      value_flag = "right";
       int FR=-1, SR=-1;
      String PrintString="";
      String first = n.f0.accept(this, argu);
      if(first==null)
          FR = reg_counter-1;
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          try {            //an 3
                    Integer.parseInt(first);
                    PrintString = PrintString +" =  icmp slt i32 " + first + ", " ;
                
          }
          catch (NumberFormatException e)   //   an x
          {
                 Nclass = Var_of_Function(visitor1,first,"int");          //Nclass is the class thas has as field the first
                  if(Nclass == null){ //an to second ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + first);     
                       reg_counter++;
                       PrintString = PrintString + " =  icmp slt i32 %_" + (reg_counter-1) + ", " ;
                    
                    }
                 else{   //an to first den einai ths synartisis
                      if(first==null){      //exei prokypsei apop syntheto expression
                          PrintString = PrintString + " =  icmp slt i32 %_" + FR + ", " ;
                      }
                      else{
                        map = (HashMap)visitor1.offsets.get(Nclass).get(0); 
                        while(map.get(first)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                        }
                        offset = (int)map.get(first) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                        reg_counter++;
                        PrintString = PrintString + " =  icmp slt i32 %_" + (reg_counter-1) + ", " ;
                      }
                  }
             }
       
      }
     catch (IOException e) {
        }
   
      type1=null;
      
      String second = n.f2.accept(this, argu);
      if(second==null)
        SR = reg_counter-1;
    
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          try {            //an 7
                 Integer.parseInt(second);
                 PrintString = PrintString  + second;
          }
          catch (NumberFormatException e)   //   an 3 + x
          {
                 Nclass = Var_of_Function(visitor1,second,"int");          //Nclass is the class thas has as field the second
                  if(Nclass == null){ //an to second ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + second);     
                       reg_counter++;
                       PrintString = PrintString  + "%_" + (reg_counter-1);
                  }
                  else{   //an to second den einai ths synartisis
                      if(second==null){      //exei prokypsei apop syntheto expression
                          PrintString = PrintString  +  "%_" +SR;
                      }
                      else{
                        map = (HashMap)visitor1.offsets.get(Nclass).get(0); 
                        while(map.get(second)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                        }
                        offset = (int)map.get(second) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                        reg_counter++;
                        PrintString = PrintString  +"%_" + (reg_counter-1);
                      }
                  }
             }
          out.println("\t%_" + reg_counter + PrintString);
          reg_counter++;
      }
       
         catch (IOException e) {
        }
  
      type1 = "boolean";
      return _ret;
   
   }
 
   public String visit(PlusExpression n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      value_flag = "right";
      int FR=-1, SR=-1;
      String PrintString="";
      String first = n.f0.accept(this, argu);
      if(first==null)
          FR = reg_counter-1;
      
     try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          try {            //an 3
                    Integer.parseInt(first);
                    PrintString = PrintString +" =  add i32 " + first + ", " ;
                
          }
          catch (NumberFormatException e)   //   an x
          {
                 Nclass = Var_of_Function(visitor1,first,"int");          //Nclass is the class thas has as field the first
                  if(Nclass == null){ //an to second ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + first);     
                       reg_counter++;
                       PrintString = PrintString + " =  add i32 %_" + (reg_counter-1) + ", " ;
                    
                    }
                 else{   //an to first den einai ths synartisis
                      if(first==null){      //exei prokypsei apop syntheto expression
                          PrintString = PrintString + " = add i32 %_" + FR + ", " ;
                      }
                      else{
                        map = (HashMap)visitor1.offsets.get(Nclass).get(0); 
                        while(map.get(first)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                        }
                        offset = (int)map.get(first) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                        reg_counter++;
                        PrintString = PrintString + " =  add i32 %_" + (reg_counter-1) + ", " ;
                      }
                  }
             }
       
      }
     catch (IOException e) {
        }
   
      type1=null;
      
      String second = n.f2.accept(this, argu);
      if(second==null)
        SR = reg_counter-1;
    
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          try {            //an 7
                 Integer.parseInt(second);
                 PrintString = PrintString  + second;
          }
          catch (NumberFormatException e)   //   an 3 + x
          {
                 Nclass = Var_of_Function(visitor1,second,"int");          //Nclass is the class thas has as field the second
                  if(Nclass == null){ //an to second ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + second);     
                       reg_counter++;
                       PrintString = PrintString  + "%_" + (reg_counter-1);
                  }
                  else{   //an to second den einai ths synartisis
                      if(second==null){      //exei prokypsei apop syntheto expression
                          PrintString = PrintString  +  "%_" +SR;
                      }
                      else{
                        map = (HashMap)visitor1.offsets.get(Nclass).get(0); 
                        while(map.get(second)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                        }
                        offset = (int)map.get(second) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                        reg_counter++;
                        PrintString = PrintString  +"%_" + (reg_counter-1);
                      }
                  }
             }
          out.println("\t%_" + reg_counter + PrintString);
          reg_counter++;
      }
       
         catch (IOException e) {
        }

      return _ret;
   }

   public String visit(MinusExpression n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      value_flag = "right";
      String PrintString="";
      int FR=-1, SR=-1;
      String first = n.f0.accept(this, argu);
      if(first==null)
          FR = reg_counter-1;
      type1 = null;
      
     try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          try {            //an 3
                    Integer.parseInt(first);
                    PrintString = PrintString +" =  sub i32 " + first + ", " ;
                
          }
          catch (NumberFormatException e)   //   an x
          {
                 Nclass = Var_of_Function(visitor1,first,"int");          //Nclass is the class thas has as field the first
                  if(Nclass == null){ //an to second ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + first);     
                       reg_counter++;
                       PrintString = PrintString + " =  sub i32 %_" + (reg_counter-1) + ", " ;
                    
                    }
                 else{   //an to first den einai ths synartisis
                      if(first==null){      //exei prokypsei apop syntheto expression
                          PrintString = PrintString + " =  sub i32 %_" + FR + ", " ;
                      }
                      else{
                        map = (HashMap)visitor1.offsets.get(Nclass).get(0); 
                        while(map.get(first)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                        }
                        offset = (int)map.get(first) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                        reg_counter++;
                        PrintString = PrintString + " =  sub i32 %_" + (reg_counter-1) + ", " ;
                      }
                  }
             }
       
      }
     catch (IOException e) {
        }
   
      type1=null;
      
      String second = n.f2.accept(this, argu);
      if(second==null)
        SR = reg_counter-1;
    
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          try {            //an 7
                 Integer.parseInt(second);
                 PrintString = PrintString  + second;
          }
          catch (NumberFormatException e)   //   an 3 + x
          {
                 Nclass = Var_of_Function(visitor1,second,"int");          //Nclass is the class thas has as field the second
                  if(Nclass == null){ //an to second ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + second);     
                       reg_counter++;
                       PrintString = PrintString  + "%_" + (reg_counter-1);
                  }
                  else{   //an to second den einai ths synartisis
                      if(second==null){      //exei prokypsei apop syntheto expression
                          PrintString = PrintString  +  "%_" +SR;
                      }
                      else{
                        map = (HashMap)visitor1.offsets.get(Nclass).get(0); 
                        while(map.get(second)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                        }
                        offset = (int)map.get(second) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                        reg_counter++;
                        PrintString = PrintString  +"%_" + (reg_counter-1);
                      }
                  }
             }
          out.println("\t%_" + reg_counter + PrintString);
          reg_counter++;
      }
       
         catch (IOException e) {
        }
      
      return _ret;
   }
   
   
   public String visit(TimesExpression n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      value_flag = "right";
       int FR=-1, SR=-1;
      String PrintString="";
      String first = n.f0.accept(this, argu);
      if(first==null)
          FR = reg_counter-1;
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          try {            //an 3
                    Integer.parseInt(first);
                    PrintString = PrintString +" =  mul i32 " + first + ", " ;
                
          }
          catch (NumberFormatException e)   //   an x
          {
                 Nclass = Var_of_Function(visitor1,first,"int");          //Nclass is the class thas has as field the first
                  if(Nclass == null){ //an to second ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + first);     
                       reg_counter++;
                       PrintString = PrintString + " =  mul i32 %_" + (reg_counter-1) + ", " ;
                    
                    }
                 else{   //an to first den einai ths synartisis
                      if(first==null){      //exei prokypsei apop syntheto expression
                          PrintString = PrintString + " =  mul i32 %_" + FR + ", " ;
                      }
                      else{
                        map = (HashMap)visitor1.offsets.get(Nclass).get(0); 
                        while(map.get(first)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                        }
                        offset = (int)map.get(first) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                        reg_counter++;
                        PrintString = PrintString + " =  mul i32 %_" + (reg_counter-1) + ", " ;
                      }
                  }
             }
       
      }
     catch (IOException e) {
        }
   
      type1=null;
      
      String second = n.f2.accept(this, argu);
      if(second==null)
        SR = reg_counter-1;
    
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          try {            //an 7
                 Integer.parseInt(second);
                 PrintString = PrintString  + second;
          }
          catch (NumberFormatException e)   //   an 3 + x
          {
                 Nclass = Var_of_Function(visitor1,second,"int");          //Nclass is the class thas has as field the second
                  if(Nclass == null){ //an to second ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + second);     
                       reg_counter++;
                       PrintString = PrintString  + "%_" + (reg_counter-1);
                  }
                  else{   //an to second den einai ths synartisis
                      if(second==null){      //exei prokypsei apop syntheto expression
                          PrintString = PrintString  +  "%_" +SR;
                      }
                      else{
                        map = (HashMap)visitor1.offsets.get(Nclass).get(0); 
                        while(map.get(second)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                        }
                        offset = (int)map.get(second) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                        reg_counter++;
                        PrintString = PrintString  +"%_" + (reg_counter-1);
                      }
                  }
             }
          out.println("\t%_" + reg_counter + PrintString);
          reg_counter++;
      }
         catch (IOException e) {
        }
   
      return _ret;
   }
      
   public String visit(ArrayLookup n, GJDepthFirst argu) {
      DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      String id = n.f0.accept(this, argu);
    
     String type = type1;
     type1=null;
     
     int array_reg=-1, size_reg=-1,index_reg=-1,array_position=-1;
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String current_class;
            int offset;
            HashMap map;
            String to_class = Var_of_Function(visitor1,id,type);
            if(type=="int[]"){
         // h periptwsi poy to id einai pedio ths synartisis
       
                if(to_class == null){ //an to id ths synartisis
                    out.println("\t%_" + reg_counter + " = load i32*, i32** %" + id);
                    array_reg = reg_counter;
                    reg_counter++;
                    out.println("\t%_" + reg_counter + " = load i32, i32* %_" + array_reg);     //fortwnw to size toy array (1o stoixeio toy pinaka)
                    size_reg = reg_counter;
                    reg_counter++;
                }
                else{
                    if(id==null){
                        array_reg = reg_counter-1;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + array_reg);     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        size_reg = reg_counter;
                        reg_counter++;
                    }
                    else{
                        map = (HashMap)visitor1.offsets.get(to_class).get(0);
                        while(map.get(id)==null){
                                to_class = visitor1.extend_classes.get(to_class);
                                map = (HashMap)visitor1.offsets.get(to_class).get(0);
                         }
                        offset = (int)map.get(id) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32**");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32*, i32** %_" + (reg_counter-1));
                        array_reg = reg_counter;
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + array_reg);     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        size_reg = reg_counter;
                        reg_counter++;
                    }
                }
            }
            else if(type=="boolean[]"){
                
                if(to_class == null){ //an to id ths synartisis
                    
                    out.println("\t%_" + reg_counter + " = load i8*, i8** %" + id);
                    array_reg = reg_counter;
                    reg_counter++;
                    out.println("\t%_" + reg_counter + " = bitcast i8* %_" + array_reg + " to i32*");
                    reg_counter++;
                    out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                    size_reg = reg_counter;
                    reg_counter++;
                }
                else{
                    if(id==null){
                        array_reg = reg_counter-1;
                        out.println("\t%_" + reg_counter + " = bitcast i8* %_" + array_reg + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        size_reg = reg_counter;
                        reg_counter++;
                    }
                    else{
                        map = (HashMap)visitor1.offsets.get(to_class).get(0);
                        while(map.get(id)==null){
                                to_class = visitor1.extend_classes.get(to_class);
                                map = (HashMap)visitor1.offsets.get(to_class).get(0);
                       }
                        offset = (int)map.get(id) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        array_reg = reg_counter;
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = bitcast i8* %_" + array_reg + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        size_reg = reg_counter;
                        reg_counter++;
                    }
                }
            }
            
       }catch (IOException e) {
        }
      
    String index = n.f2.accept(this, argu);
   
    if(type == "int[]")
        type1 = "int";
    else
        type1 = "boolean";
    
   try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String current_class;
            int offset;
            HashMap map;
                try { 
                     Integer.parseInt(index);
                     out.println("\t%_" + reg_counter + " = icmp sge i32 "+ index + ", 0");  //index >=0
                     reg_counter++;
                     out.println("\t%_" + reg_counter + " = icmp slt i32 " + index + ", %_" + size_reg); //index < size_array
                     reg_counter++;
                }
                catch (NumberFormatException e)
               {
                      //elegxos gia to an h metabliti index einai pedio tis sinartisis i kapoias klasis
                      current_class = Var_of_Function(visitor1,index,"int");          //currentclass is the class thas has as field the index
                      if(current_class == null){ //an to expr ths synartisis

                           out.println("\t%_" + reg_counter + " = load i32, i32* %" + index);
                           index_reg = reg_counter;
                          reg_counter++;
                           out.println("\t%_" + reg_counter + " = icmp sge i32 %_"+ index_reg + ", 0");  //index >=0
                           reg_counter++;
                           out.println("\t%_" + reg_counter + " = icmp slt i32 %_" + index_reg + ", %_" + size_reg); //index < size_array
                           reg_counter++;
                       }
                       else{//an to index den einai ths synartisis
                           if(index==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                                  index_reg = reg_counter - 1;
                                  out.println("\t%_" + reg_counter + " = icmp sge i32 %_"+ index_reg + ", 0");  //index >=0
                                  reg_counter++;
                                  out.println("\t%_" + reg_counter + " = icmp slt i32 %_" + index_reg + ", %_" + size_reg); //index < size_array
                                  reg_counter++;
                           }
                          else{
                                  map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                  while(map.get(index)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                  }
                                  offset = (int)map.get(index) +8;
                                  out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                  reg_counter++;
                                  out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                                  reg_counter++;
                                  out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                                  index_reg = reg_counter;
                                  reg_counter++;
                                  out.println("\t%_" + reg_counter + " = icmp sge i32 %_"+ index_reg + ", 0");  //index >=0
                                  reg_counter++;
                                  out.println("\t%_" + reg_counter + " = icmp slt i32 %_" + index_reg + ", %_" + size_reg); //index < size_array
                                  reg_counter++;
                          }
                      }
                  }

                oob_counter++;
                out.println("\t%_" + reg_counter + " = and i1 %_" + (reg_counter-1) + ", %_" + (reg_counter-2));    //na isxyoun kai oi 2 periorismoi
                out.println("\tbr i1 %_" + reg_counter + ", label %oob_ok_" + oob_counter + ", label %oob_err_" + oob_counter);
                reg_counter++;
                out.println("\n\toob_err_" + oob_counter + ":");
                out.println("\tcall void @throw_oob()");
                out.println("\tbr label %oob_ok_" + oob_counter);
                out.println("\n\toob_ok_" +oob_counter+ ":");
                oob_counter++;
                if(type1=="int"){
                    try {                                                       //prosthetw 1 sto index giati sthn 1h thesi einai to size
                         Integer.parseInt(index);
                         out.println("\t%_" + reg_counter + " = add i32 1, " + index);
                         reg_counter++;
                    }
                    catch (NumberFormatException e)
                   {
                       out.println("\t%_" + reg_counter + " = add i32 1, %_" + index_reg);
                       reg_counter++;
                   }

                    out.println("\t%_" + reg_counter +" = getelementptr i32, i32* %_" + array_reg + ", i32 %_" + (reg_counter-1));
                    array_position = reg_counter;
                    reg_counter++;
                    if(value_flag=="right"){
                        out.println("\t%_" + reg_counter +" = load i32, i32* %_" + (reg_counter-1));
                        reg_counter++;
                    }
            }
            else if (type1=="boolean"){
                try {                                                       //prosthetw 1 sto index giati sthn 1h thesi einai to size
                         Integer.parseInt(index);
                         out.println("\t%_" + reg_counter + " = add i32 4, " + index);
                         reg_counter++;
                    }
                    catch (NumberFormatException e)
                   {
                       out.println("\t%_" + reg_counter + " = add i32 4, %_" + index_reg);
                       reg_counter++;
                   }

                    out.println("\t%_" + reg_counter +" = getelementptr i8, i8* %_" + array_reg + ", i32 %_" + (reg_counter-1));
                    array_position = reg_counter;
                    reg_counter++;
                    if(value_flag=="right"){
                        out.println("\t%_" + reg_counter +" = load i8, i8* %_" + (reg_counter-1));
                        reg_counter++;
                        out.println("\t%_" + reg_counter + "= trunc i8 %_" + (reg_counter-1) + " to i1");
                        reg_counter++;
                    }
            }
        } catch (IOException e) {
        }
     
      return _ret;
   }
    
   
   public String visit(ArrayLength n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      String exp = n.f0.accept(this, argu);
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String current_class;
            int offset;
            HashMap map;
            String to_class = Var_of_Function(visitor1,exp,type1);
            if(type1=="int[]"){
         // h periptwsi poy to exp einai pedio ths synartisis
       
                if(to_class == null){ //an to exp ths synartisis
                    out.println("\t%_" + reg_counter + " = load i32*, i32** %" + exp);
                    reg_counter++;
                    out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                    reg_counter++;
                }
                else{
                    if(exp==null){
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        reg_counter++;
                    }
                    else{
                        map = (HashMap)visitor1.offsets.get(to_class).get(0);
                        while(map.get(exp)==null){
                             to_class = visitor1.extend_classes.get(to_class);
                             map = (HashMap)visitor1.offsets.get(to_class).get(0);
                        }
                        offset = (int)map.get(exp) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32**");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32*, i32** %_" + (reg_counter-1));
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        reg_counter++;
                    }
                }
            }
            else if(type1=="boolean[]"){
                if(to_class == null){ //an to id ths synartisis
                    out.println("\t%_" + reg_counter + " = load i8*, i8** %" + exp);
                    reg_counter++;
                    out.println("\t%_" + reg_counter + " = bitcast i8* %_" + (reg_counter-1) + " to i32*");
                    reg_counter++;
                    out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                    reg_counter++;
                }
                else{
                    if(exp==null){
                        out.println("\t%_" + reg_counter + " = bitcast i8* %_" + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        reg_counter++;
                    }
                    else{
                        map = (HashMap)visitor1.offsets.get(to_class).get(0);
                        while(map.get(exp)==null){
                             to_class = visitor1.extend_classes.get(to_class);
                             map = (HashMap)visitor1.offsets.get(to_class).get(0);
                        }
                        offset = (int)map.get(exp) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = bitcast i8* %_" + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        reg_counter++;
                    }
                }
            }
            
       }catch (IOException e) {
        }
      type1 = "int";
      return _ret;
   }
  
   
   public String visit(MessageSend n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
     newAlloc_flag = false;
      String _ret=null;
      String id = n.f0.accept(this, argu);
      String id_type=type1;
      if(id == "this"){
          id = classname; // the global var
          type1 = "class";
      }
      String nameclass,namefunction;
      if(!"class".equals(type1) ){
          nameclass= new String(type1);
          Typecheck(type1, argu);
          
      }
      else
        nameclass= new String(id);  
      
      
      int object_reg=-1;
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String current_class;
            int offset;
            HashMap map;
            if(id==null  ){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
            
                   object_reg = reg_counter-1;
                   out.println("\t%_" + reg_counter + " = bitcast i8* %_" +object_reg +" to i8***");
                   reg_counter++;
            }
            else if(newAlloc_flag==true){
                    object_reg = reg_counter-3;
                    newAlloc_flag=false;
                    out.println("\t%_" + reg_counter + " = bitcast i8* %_" +object_reg +" to i8***");
                    reg_counter++;
            }
            else if(id==classname){
                
                object_reg = -1;
                out.println("\t%_" + reg_counter + " = bitcast i8* %this to i8***");
                reg_counter++;
            }
             else{   
               
                current_class = Var_of_Function(visitor1,id,id_type);          //currentclass is the class thas has as field the id
                if(current_class == null){ //an to id ths synartisis
                     out.println("\t%_" + reg_counter + " = load i8*, i8** %" + id);
                     reg_counter++;

                }
                 else{      //an to id den einai ths synartisis
                        
                        map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                        while(map.get(id)==null){
                             current_class = visitor1.extend_classes.get(current_class);
                             map = (HashMap)visitor1.offsets.get(current_class).get(0);
                        }
                        offset = (int)map.get(id) +8;
                         out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                         reg_counter++;
                         out.println("\t%_" + reg_counter + " = bitcast i8* %_" +(reg_counter-1) +" to i8**");   
                         reg_counter++;
                         out.println("\t%_" + reg_counter + " = load i8*, i8** %_" + (reg_counter-1));
                         reg_counter++;
                         
                  }
                object_reg = reg_counter-1;
                out.println("\t%_" + reg_counter + " = bitcast i8* %_" +object_reg +" to i8***");
                reg_counter++;
           }
            
            
            out.println("\t%_" + reg_counter + " = load i8**, i8*** %_" + (reg_counter-1));         // Load v table
            reg_counter++;
            
      } catch (IOException e) {
            //exception handling left as an exercise for the reader
        }
      
      type1=null;
    namefunction = n.f2.accept(this, argu);
     
    if(length==0){
        length=1;
        new_param_counter = new int[length];
        fun_call= new String[length];
        class_call = new String[length];
        fun_call[length-1] = namefunction;
        class_call[length-1] = nameclass;
        new_param_counter[length-1] = -1;
        sum_args = new int[length];
        sum_args[length-1] = 0;
        new_function_call_buffer = new String[length];
        new_function_call_buffer[length-1]="";
    }
    else{
        param_counter = new int[length];
        for(int i = 0; i < length ; i++){
            param_counter[i] = new_param_counter[i];
        }
        
        prev_fun_call = new String[length];
        for(int i = 0; i < length ; i++){
            prev_fun_call[i] = fun_call[i];
        }
        
        prev_class_call = new String[length];
        for(int i = 0; i < length ; i++){
            prev_class_call[i] = class_call[i];
        }
        
        prev_sum_args = new int[length];
        for(int i = 0; i < length ; i++){
            prev_sum_args[i] = sum_args[i];
        }
        
        function_call_buffer = new String[length];
        for(int i = 0; i < length ; i++){
            function_call_buffer[i] = new_function_call_buffer[i];
        }
        
        length++;
        
        new_param_counter = new int[length];
        for(int i = 0; i < (length-1) ; i++){               //ta antigrafw ola ektos apo tin teleytaia thesi
            new_param_counter[i] = param_counter[i];
        }
        new_param_counter[length-1] = -1;
      
       
        fun_call = new String[length];
        for(int i = 0; i < (length-1) ; i++){               //ta antigrafw ola ektos apo tin teleytaia thesi
            fun_call[i] = prev_fun_call[i];
        }
        fun_call[length-1] = namefunction;
        
      
        class_call = new String[length];
        for(int i = 0; i < (length-1) ; i++){               //ta antigrafw ola ektos apo tin teleytaia thesi
            class_call[i] = prev_class_call[i];
        }
        class_call[length-1] = nameclass;
        
        sum_args = new int[length];
        for(int i = 0; i < (length-1) ; i++){               //ta antigrafw ola ektos apo tin teleytaia thesi
            sum_args[i] = prev_sum_args[i];
        }
        sum_args[length-1] = -1;
        
        new_function_call_buffer = new String[length];
        for(int i = 0; i < (length-1) ; i++){               //ta antigrafw ola ektos apo tin teleytaia thesi
            new_function_call_buffer[i] = function_call_buffer[i];
        }
        new_function_call_buffer[length-1] = "";
    }
    
      String return_type = ExistanceCheck(argu, nameclass, namefunction);   //metraw posa args prepei na exei kai poion typo epistrofis exei
      
       try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String current_class=nameclass;
            int offset;
            HashMap map;
            
            map = (HashMap)visitor1.offsets.get(current_class).get(1);
       
            while(map.get(namefunction) ==null){
                current_class = visitor1.extend_classes.get(current_class);
                map = (HashMap)visitor1.offsets.get(current_class).get(1);
            }
           offset = (int)map.get(namefunction) /8;
            out.println("\t%_" + reg_counter + " = getelementptr i8*, i8** %_" + (reg_counter-1) + ", i32 " + offset);
            reg_counter++;
            out.println("\t%_" + reg_counter + " = load i8*, i8** %_" + (reg_counter-1) );
            reg_counter++;
            
      } catch (IOException e) {
     }
      
        MessageSendWrite(visitor1, nameclass, namefunction);
        
            
       String ret = FindType(return_type);
       if (ret=="i8")
           ret="i1";
       if(object_reg==-1)
           new_function_call_buffer[length-1] = " = call " + ret + " %_" + (reg_counter-1) + "(i8* %this";
       else
            new_function_call_buffer[length-1] = " = call " + ret + " %_" + (reg_counter-1) + "(i8* %_" + object_reg;
          
       value_flag = "right";
        n.f4.accept(this, argu);
        
        try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
                out.print("\t%_" + reg_counter );
                out.print(new_function_call_buffer[length-1]);
                out.println(")");
                reg_counter++;
                bool_array_reg = reg_counter-1;
            } catch (IOException e) {
            //exception handling left as an exercise for the reader
        }
        
       
  
        if(sum_args[length-1] ==0 && new_param_counter[length-1] == -1){
            
        }
       
      
        length--;
        if(length==0){
            new_param_counter=param_counter =sum_args= prev_sum_args= null;
            fun_call= prev_fun_call = class_call = prev_class_call=null;
            new_function_call_buffer=function_call_buffer=null;
        }
        else{
            new_param_counter = new int[length];
            for(int i = 0; i < length ; i++){
                new_param_counter[i] = param_counter[i];
            }
            
            fun_call = new String[length];
            for(int i = 0; i < length ; i++){
                fun_call[i] = prev_fun_call[i];
            }
            
            class_call = new String[length];
            for(int i = 0; i < length ; i++){
                class_call[i] = prev_class_call[i];
            }
            
            sum_args = new int[length];
            for(int i = 0; i < length ; i++){
                sum_args[i] = prev_sum_args[i];
            }
            
            new_function_call_buffer= new String[length];
            for(int i = 0; i < length ; i++){
                new_function_call_buffer[i] = function_call_buffer[i];
            }
        }
      
      
      type1 = return_type;
      return _ret;
   }
   
   public String ExistanceCheck(GJDepthFirst argu, String nameclass,String  namefunction){
            DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
            ListIterator<List> Tableitr=visitor1.SymbolTable.listIterator();
            ListIterator  listitr=null;
            Object extend_vars =  null,fun_vars=null;
            sum_args[length-1] =0;
            
            while(nameclass != null){
                
                Tableitr=visitor1.SymbolTable.listIterator();
                while(Tableitr.hasNext()) {

                   listitr=Tableitr.next().listIterator();
                   while(listitr.hasNext()) {

                        HashMap next_map = (HashMap)listitr.next();
                        extend_vars = next_map.get(nameclass);                  //class
                        if(extend_vars !=null){
                            while(listitr.hasNext()) {
                                    next_map = (HashMap)listitr.next();
                                    
                                    fun_vars = next_map.get(namefunction);                  //function
                                    if(fun_vars!=null){                                          // h function einai member tis klasis
                                        
                                        while(((HashMap)fun_vars).get("chrysa_arg" + String.valueOf(sum_args[length-1])) != null){
                                            sum_args[length-1]++;
                                        }
                                        return (String)((HashMap)fun_vars).get("return_value");     // ton typo epistrofis ths synarthshs
                                    }
                            }
                        }
                        break;
                   }
                }
                nameclass = visitor1.extend_classes.get(nameclass);
            }
       
            return null;
    }
   
   
   public String Argument_check(GJDepthFirst argu){
     
      DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      ListIterator<List> Tableitr=visitor1.SymbolTable.listIterator();
      ListIterator  listitr=null;
      Object extend_vars =  null,fun_vars=null;
      String nameclass = class_call[length-1];
      String arg_type = null;
      
       while(nameclass != null && arg_type==null){
                
            Tableitr=visitor1.SymbolTable.listIterator();
            while(Tableitr.hasNext()) {

                   listitr=Tableitr.next().listIterator();
                   while(listitr.hasNext()) {

                        HashMap next_map = (HashMap)listitr.next();
                        extend_vars = next_map.get(nameclass);                  //class
                        if(extend_vars !=null){
                            
                            while(listitr.hasNext()) {
                                    next_map = (HashMap)listitr.next();
                                    
                                    fun_vars = next_map.get(fun_call[length-1]);                  //function
                                    if(fun_vars!=null){                                                  // h function einai member tis klasis
                                       
                                       arg_type = (String)((HashMap)fun_vars).get("chrysa_arg"+String.valueOf(new_param_counter[length-1]));     // to 1o arg ths synarthshs
                                       return arg_type;
                                    }
                            }
                        }
                        break;
                }
            }
            nameclass = visitor1.extend_classes.get(nameclass);
       }
       return null;
   }
   
    public String visit(Expression n, GJDepthFirst argu) {
      
        String exp = n.f0.accept(this, argu);
         return exp;
   }
    
    
    
   public String visit(ExpressionList n, GJDepthFirst argu) {
       
    
       if(sum_args[length-1]==0){
           return null;
       }
       String _ret=null;
       newAlloc_flag =false;
       new_param_counter[length-1] = 0;
      String exp = n.f0.accept(this, argu);

        if(new_param_counter!=null   && new_param_counter[length-1] > -1){
            String param_type = Argument_check(argu);
            DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
          
            new_param_counter[length-1] ++;
            String type = FindType(param_type);
           
            try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
                String Nclass;
                HashMap map;
                int offset;
                if(exp=="true"){
                    out.println("\t%_" + reg_counter + " = zext i1 1 to i8");
                    new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", i8 %_" +reg_counter;
                    reg_counter++;
                }
                else if(exp=="false"){
                    out.println("\t%_" + reg_counter + " = zext i1 0 to i8");
                    new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", i8 %_" +reg_counter;
                    reg_counter++;
                }
                else if(exp==null){
                     if (newAlloc_flag==true){
                             new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", " + type + " %_" + (alloc_reg_counter-3);
                    }
                     else{
                        if(type=="i8"){
                            out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                            reg_counter++;
                           
                        }
                        new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", " + type + " %_" + (reg_counter-1); 
                     }
                }
                else{
                    try {
                        Integer.parseInt(exp);
                        new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", i32 " + exp;
                    }
                    catch (NumberFormatException e)
                    {
                        if(exp==classname){ //this
                            new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", i8* %this";
                        }
                        else if (newAlloc_flag==true){
                                 
                                 new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", " + type + " %_" + (alloc_reg_counter-3);
                             }
                        else{
                          
                            Nclass = Var_of_Function(visitor1,exp,param_type);          //Nclass is the class thas has as field the exp
                            if(Nclass == null){
                                out.println("\t%_" + reg_counter + " = load " + type + ", " + type + "* %" + exp); 
                                reg_counter++;
                                // !!!!! isws prepei an einai boolean na to kanw cast se i1

                                new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", " + type + " %_" + (reg_counter-1);
                            }
                            else{
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                                while(map.get(exp)==null){
                                    Nclass = visitor1.extend_classes.get(Nclass);
                                    map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                                }
                                offset = (int)map.get(exp) +8;
                                out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                reg_counter++;
                                if(type=="i32"){
                                    out.println("\t%_" + reg_counter + " = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load " + type + ", " + type + "* %_" + (reg_counter-1));
                                    reg_counter++;
                                }
                                else if(type=="i32*"){
                                    out.println("\t%_" + reg_counter + " = bitcast i8* %_"  + (reg_counter-1) + " to i32**");
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load " + type + ", " + type + "* %_" + (reg_counter-1));
                                    reg_counter++;
                                }
                                if(type=="i8*" && param_type!="boolean[]"){
                                    out.println("\t%_" + reg_counter + " = bitcast i8* %_"  + (reg_counter-1) + " to i8**");
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load " + type + ", " + type + "* %_" + (reg_counter-1));
                                    reg_counter++;
                                }
                                
                                 new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", " + type + " %_" + (reg_counter-1);
                            }
                        }
                    }
                }
            } catch (IOException e) {
            }
        }
   
       n.f1.accept(this, argu);
      return _ret;
   }

  
   
   public String visit(ExpressionTail n, GJDepthFirst argu) {
      
      return n.f0.accept(this, argu);
   }

  
   public String visit(ExpressionTerm n, GJDepthFirst argu) {
      
      String _ret=null;
      n.f0.accept(this, argu);
      newAlloc_flag = false;
      String exp = n.f1.accept(this, argu);
      
        if(new_param_counter!=null   && new_param_counter[length-1] > -1){
            String param_type = Argument_check(argu);
            DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
            
            new_param_counter[length-1] ++;
            
            String type = FindType(param_type);
           
            try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
                String Nclass;
                HashMap map;
                int offset;
                if(exp=="true"){
                    out.println("\t%_" + reg_counter + " = zext i1 1 to i8");
                    new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", i8 %_" +reg_counter;
                    reg_counter++;
                }
                else if(exp=="false"){
                  out.println("\t%_" + reg_counter + " = zext i1 0 to i8");
                    new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", i8 %_" +reg_counter;
                    reg_counter++;
                }
                else if(exp==null){
                    if (newAlloc_flag==true){
                             new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", " + type + " %_" + (alloc_reg_counter-3);
                    }
                    else{
                        if(type=="i8"){
                            out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                            reg_counter++;
                            
                        }
                        new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", " + type + " %_" + (reg_counter-1); 
                    }
                    
                }
                else{
                    try {
                        Integer.parseInt(exp);
                        new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", i32 " + exp;
                    }
                    catch (NumberFormatException e)
                    {
                        if(exp==classname){ //this
                            new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", i8* %this";
                        }
                        else if (newAlloc_flag==true){
                                 new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", " + type + " %_" + (alloc_reg_counter-3);
                             }
                        else{
                            Nclass = Var_of_Function(visitor1,exp,param_type);          //Nclass is the class thas has as field the exp
                            if(Nclass == null){
                                out.println("\t%_" + reg_counter + " = load " + type + ", " + type + "* %" + exp); 
                                reg_counter++;
                                // !!!!! isws prepei an einai boolean na to kanw cast se i1

                                new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", " + type + " %_" + (reg_counter-1);
                            }
                            else{
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                                while(map.get(exp)==null){
                                    Nclass = visitor1.extend_classes.get(Nclass);
                                    map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                                }
                                offset = (int)map.get(exp) +8;
                                out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                reg_counter++;
                                if(type=="i32"){
                                    out.println("\t%_" + reg_counter + " = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load " + type + ", " + type + "* %_" + (reg_counter-1));
                                    reg_counter++;
                                }
                                else if(type=="i32*"){
                                    out.println("\t%_" + reg_counter + " = bitcast i8* %_"  + (reg_counter-1) + " to i32**");
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load " + type + ", " + type + "* %_" + (reg_counter-1));
                                    reg_counter++;
                                }
                                if(type=="i8*" && param_type!="boolean[]"){
                                    out.println("\t%_" + reg_counter + " = bitcast i8* %_"  + (reg_counter-1) + " to i8**");
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load " + type + ", " + type + "* %_" + (reg_counter-1));
                                    reg_counter++;
                                }
                                
                                 new_function_call_buffer[length-1] = new_function_call_buffer[length-1] + ", " + type + " %_" + (reg_counter-1);
                            }
                        }
                    }
                }
            } catch (IOException e) {
            }
        }
      return _ret;
   }
   
   
   public String visit(BooleanArrayAllocationExpression n, GJDepthFirst argu) {
      String _ret=null;
     
      DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String size = n.f3.accept(this, argu);
    
      bool_array_reg = -1;
     type1 = "boolean[]";
     int size_reg;
     try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String Nclass;
            HashMap map;
            int offset;
            try {
                 Integer.parseInt(size);
                 out.println("\t%_" +  reg_counter + " = add i32 4, " + size );
                 reg_counter++;
            }
            catch (NumberFormatException e)
            {
                  Nclass = Var_of_Function(visitor1,size,"int");          //Nclass is the class thas has as field the size
                  if(Nclass == null){ //an to size ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + size); 
                       reg_counter++;
                       out.println("\t%_" +  reg_counter + " = add i32 4, %_" + (reg_counter-1) );
                       reg_counter++;
                   }
                   else{//an to size den einai ths synartisis
                      if(size==null){
                          out.println("\t%_" +  reg_counter + " = add i32 4, %_" + (reg_counter-1));
                          reg_counter++;
                      }
                      else{
                         map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                         while(map.get(size)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                         }
                         offset = (int)map.get(size) +8;
                         out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                         reg_counter++;
                         out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                         reg_counter++;
                         out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                         reg_counter++;
                         out.println("\t%_" +  reg_counter + " = add i32 4, %_" + (reg_counter-1));
                         reg_counter++;
                      }
                  }
            }
            
            nsz_counter++;
            size_reg = (reg_counter-1);
            out.println("\t%_" +  reg_counter + " = sub i32 %_" + size_reg + ", 4");
            int contents_size_reg = reg_counter;
            reg_counter++;
            out.println("\t%_" +  reg_counter + " = icmp sge i32 %_" + size_reg + ", 4");    //new_size>=4
            out.println("\tbr i1 %_" + reg_counter + ", label %nsz_ok_" +nsz_counter+ ", label %nsz_err_" +nsz_counter);
            reg_counter++;
            out.println("\n\tnsz_err_" +nsz_counter +":");
            out.println("\tcall void @throw_nsz()");
            out.println("\tbr label %nsz_ok_" + nsz_counter);
            out.println("\n\tnsz_ok_" +nsz_counter+":");
            nsz_counter++;
            out.println("\t%_" +  reg_counter + " = call i8* @calloc(i32 %_" +  size_reg +", i32 1)");
            reg_counter++;
            out.println("\t%_" +  reg_counter + " = bitcast i8* %_" + (reg_counter-1) +" to i32*");
            reg_counter++;
            out.println("\tstore i32 %_" + contents_size_reg +", i32* %_" +  (reg_counter-1));        //apothikeysh sth 1h thesi to size toy pinaka
            bool_array_reg = reg_counter-2;
     } catch (IOException e) {
            //exception handling left as an exercise for the reader
        }
      return _ret;
   }

   
   public String visit(IntegerArrayAllocationExpression n, GJDepthFirst argu) {
      String _ret=null;
    DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String size = n.f3.accept(this, argu);
     
     type1 = "int[]";
     int size_reg;
     try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String Nclass;
            HashMap map;
            int offset;
            try {
                 Integer.parseInt(size);
                 out.println("\t%_" +  reg_counter + " = add i32 1, " + size );
                 reg_counter++;
            }
            catch (NumberFormatException e)
            {
                  Nclass = Var_of_Function(visitor1,size,"int");          //Nclass is the class thas has as field the size
                  if(Nclass == null){ //an to size ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + size); 
                       reg_counter++;
                       out.println("\t%_" +  reg_counter + " = add i32 1, %_" + (reg_counter-1) );
                       reg_counter++;
                   }
                   else{//an to size den einai ths synartisis
                      if(size==null){
                          out.println("\t%_" +  reg_counter + " = add i32 1, %_" + (reg_counter-1));
                          reg_counter++;
                      }
                      else{
                         map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                         while(map.get(size)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                         }
                         offset = (int)map.get(size) +8;
                         out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                         reg_counter++;
                         out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                         reg_counter++;
                         out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                         reg_counter++;
                         out.println("\t%_" +  reg_counter + " = add i32 1, %_" + (reg_counter-1));
                         reg_counter++;
                      }
                  }
            }
            nsz_counter++;
            size_reg = (reg_counter-1);
            out.println("\t%_" +  reg_counter + " = sub i32 %_" + size_reg + ", 1");
            int contents_size_reg = reg_counter;
            reg_counter++;
            out.println("\t%_" +  reg_counter + " = icmp sge i32 %_" + size_reg + ", 1");    //new_size>=1
            out.println("\tbr i1 %_" + reg_counter + ", label %nsz_ok_" +nsz_counter+ ", label %nsz_err_" +nsz_counter);
            reg_counter++;
            out.println("\n\tnsz_err_" +nsz_counter +":");
            out.println("\tcall void @throw_nsz()");
            out.println("\tbr label %nsz_ok_" + nsz_counter);
            out.println("\n\tnsz_ok_" +nsz_counter+":");
            nsz_counter++;
            out.println("\t%_" +  reg_counter + " = call i8* @calloc(i32 %_" +  size_reg +", i32 4)");
            reg_counter++;
            out.println("\t%_" +  reg_counter + " = bitcast i8* %_" + (reg_counter-1) +" to i32*");
            reg_counter++;
            out.println("\tstore i32 %_" + contents_size_reg +", i32* %_" +  (reg_counter-1));        //apothikeysh sth 1h thesi to size toy pinaka
     } catch (IOException e) {
        }
      return _ret;
   }
   
   
   public int SizeofObject(DefCollectVisitor visitor, String id){
       
       while(id!=null && id!= visitor.Mainclass){
            HashMap map = (HashMap)visitor.offsets.get(id).get(0);
            String var=null;
            int offset=-1;
           for (Iterator it =map.entrySet().iterator(); it.hasNext();) {
               Map.Entry mapElement = (Entry)it.next();
               var = (String)mapElement.getKey();
               offset =(int)mapElement.getValue();
           }
           ListIterator<List> Tableitr=visitor.SymbolTable.listIterator();
           ListIterator  listitr=null;
           Object extend_vars =  null;
           String var_type=null;

           
           if(var!=null){                                                                                //an h klasi exei toylaxiston ena field

                Tableitr=visitor.SymbolTable.listIterator();
                while(Tableitr.hasNext()) {

                        listitr=Tableitr.next().listIterator();
                        while(listitr.hasNext()) {

                             HashMap next_map = (HashMap)listitr.next();
                             extend_vars = next_map.get(id);                  //class
                             if(extend_vars !=null){
                                 var_type = (String)((HashMap)extend_vars).get(var);
                                 break;
                             }
                        }
                }       
               
               if(var_type=="int")
                   offset+= 4;
               else if(var_type=="boolean")
                   offset+= 1;
               else 
                   offset+= 8;
               return offset;
           }
           else{                                                                                     // an h klasi den exei field
                id = visitor.extend_classes.get(id);
           }
       }
       return 0;
   }
   
   public String visit(AllocationExpression n, GJDepthFirst argu) {
       
      DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      String id = n.f1.accept(this, argu);
      String id_type = type1;
      if(type1!="class"){
          Typecheck(type1, argu);
            type1 = id_type;
      }
      int size = SizeofObject(visitor1, id) + 8;
      try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            out.println("\t%_" + reg_counter + " = call i8* @calloc(i32 1, i32 " + size + ")");
            reg_counter ++;
            out.println("\t%_" + reg_counter + " = bitcast i8* %_" + (reg_counter-1) + " to i8***");
            reg_counter++;
            int funcs = visitor1.func_counter.get(id);
            out.println("\t%_" + reg_counter + " = getelementptr [" + funcs + " x i8*], [" + funcs + " x i8*]* @." + id + "_vtable, i32 0, i32 0");
            out.println("\tstore i8** %_" + reg_counter + ", i8*** %_" + (reg_counter-1));
            reg_counter++;
        } catch (IOException e) {
        }
      alloc_reg_counter= reg_counter;
      newAlloc_flag = true;
      return id;
   }
   
   public String visit(BooleanArrayType n, GJDepthFirst argu) {
        type1 = "boolean[]";
        return "boolean[]";
   }
    
    public String visit(IntegerArrayType n, GJDepthFirst argu) {
         type1 = "int[]";
      return "int[]";
   }
   
    
   public String visit(BooleanType n, GJDepthFirst argu) {
       type1 = "boolean";
      return n.f0.accept(this, argu);
   }

   
   public String visit(IntegerType n, GJDepthFirst argu) {
       type1 = "int";
      return n.f0.accept(this, argu);
   }
   
   
   public String visit(Type n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
       String type = n.f0.accept(this, argu);
     
      
      if(type1 == "int" || type1 == "boolean" || type1 == "int[]" || type1 == "boolean[]" || type1 == "class" || type1 == "function" )
          return type;
      else if((type1 == "String[]") && (classname == visitor1.Mainclass))
          return type;
      else{
            
            ListIterator<List> Tableitr=visitor1.SymbolTable.listIterator();
            ListIterator  listitr=null;
            
            while(Tableitr.hasNext()) {
                listitr=Tableitr.next().listIterator();

                 HashMap next_map = (HashMap)listitr.next();
                       
                 if (next_map.get(type1) != null){
                       type1 = "class";
                        return type;
                 }
            }
        
            return type;
      }
   }
   
   
   public String visit(TrueLiteral n, GJDepthFirst argu) {
       type1 ="boolean";
      return n.f0.accept(this, argu);
   }

   
   public String visit(FalseLiteral n, GJDepthFirst argu) {
        type1 ="boolean";
      return n.f0.accept(this, argu);
   }
   
   
   public String visit(NotExpression n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
     value_flag = "right";
      String _ret=null;
      String exp = n.f1.accept(this, argu);
   
     type1 = "boolean";
     
     try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          if (exp == "true"  ){
                  out.println("\t%_" + reg_counter + " = alloca i8");
                  out.println("\tstore i8 0, i8* %_"+ reg_counter );        // to antitheto epeidh eimaste sto not
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));  
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                  reg_counter++;
          }
          else if(exp=="false"){
                  out.println("\t%_" + reg_counter + " = alloca i8");
                  out.println("\tstore i8 1, i8* %_"+ reg_counter );        // to antitheto epeidh eimaste sto not
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));     
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                  reg_counter++;
          }
          else if(exp!=null){
                 Nclass = Var_of_Function(visitor1,exp,"boolean");          //Nclass is the class thas has as field the first
                 if(Nclass == null){ //an to exp ths synartisis
                       out.println("\t%_" + reg_counter + " = load i8, i8* %" + exp);     
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = xor i1 %_" + (reg_counter-1) + ", true");
                       reg_counter++;
                    }
                    else{   //an to exp den einai ths synartisis
                       map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                       while(map.get(exp)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                        }
                       offset = (int)map.get(exp) +8;
                       out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = xor i1 %_" + (reg_counter-1) + ", true");
                       reg_counter++;
                  }
                 
          }
          else if (exp==null){
              out.println("\t%_" + reg_counter + " = xor i1 %_" + (reg_counter-1) + ", true");
              reg_counter++;
          }
      }
         catch (IOException e) {
        }
      return _ret;
   }
   
   
   public String visit(Clause n, GJDepthFirst argu) {
     
      String clause = n.f0.accept(this, argu);
      return clause;
   }
   
   public String visit(IfStatement n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      value_flag = "right";
      first_reg = sec_reg = -1;
      String cond = n.f2.accept(this, argu);
      first_reg = sec_reg = -1;
      
       if_counter++;
      int if_then_counter = if_counter;
      
    
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            HashMap map;
            String current_class;
            int offset;
           
            if(cond=="true"){
                out.println("\tbr i1 " + 1 + ", label %if_then_" + if_then_counter +", label %if_else_" +if_then_counter+"\n");
            }
            else if(cond=="false"){
                out.println("\tbr i1 " + 0 + ", label %if_then_" + if_then_counter +", label %if_else_" +if_then_counter+"\n");
            }
            else{
                current_class = Var_of_Function(visitor1,cond,"boolean");          //currentclass is the class thas has as field the cond
                if(current_class == null){ //an to expr ths synartisis
                       out.println("\t%_" + reg_counter + " = load i8, i8* %" + cond);
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                       reg_counter++;
                       out.println("\tbr i1 %_" + (reg_counter-1) + ", label %if_then_" + if_then_counter +", label %if_else_" +if_then_counter+"\n");
                }
                else{//an to cond den einai ths synartisis
                       if(cond==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                           out.println("\tbr i1 %_" + (reg_counter-1) + ", label %if_then_" + if_then_counter +", label %if_else_" +if_then_counter+"\n");
                        }
                       else{
                           map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                           while(map.get(cond)==null){
                                current_class = visitor1.extend_classes.get(current_class);
                                map = (HashMap)visitor1.offsets.get(current_class).get(0);
                            }
                           offset = (int)map.get(cond) +8;
                           out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                           reg_counter++;
                           out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));
                           reg_counter++;
                           out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                           reg_counter++;
                           out.println("\tbr i1 %_" + (reg_counter-1) + ", label %if_then_" + if_then_counter +", label %if_else_" +if_then_counter+"\n");
                       }
                }
            }
            out.println("\tif_then_" +if_then_counter+":");
      
      } catch (IOException e) {
      }
      String ifStat = n.f4.accept(this, argu);
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            out.println("\tbr label %if_end_" + if_then_counter + "\n");
            out.println("\tif_else_" + if_then_counter + ":");
      
      } catch (IOException e) {
      }
      
      String elseStat = n.f6.accept(this, argu);
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            out.println("\tbr label %if_end_" +if_then_counter+ "\n");
            out.println("\tif_end_" + if_then_counter + ":");
      
      } catch (IOException e) {
      }
      
      if_counter++;
      return _ret;
   }
   
   
   public String visit(WhileStatement n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      value_flag = "right";
      
      while_counter++;
      int while_then_counter = while_counter;
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            out.println("\tbr label %while_" + while_then_counter + "\n");
            out.println("\twhile_" + while_then_counter + ":");
      } catch (IOException e) {
      }
      
      first_reg = sec_reg = -1;
      String expr = n.f2.accept(this, argu);
      first_reg = sec_reg = -1;
      
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
          
             HashMap map;
            String current_class;
            int offset;
           
            if(expr=="true"){
                out.println("\tbr i1 " +1 + ", label %while_then_" + while_then_counter + ", label %while_end_" + while_then_counter + "\n");
            }
            else if(expr=="false"){
                out.println("\tbr i1 " + 0 + ", label %while_then_" + while_then_counter + ", label %while_end_" + while_then_counter + "\n");
            }
            else{
                current_class = Var_of_Function(visitor1,expr,"boolean");          //currentclass is the class thas has as field the cond
                if(current_class == null){ //an to expr ths synartisis
                       out.println("\t%_" + reg_counter + " = load i8, i8* %" + expr);
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                       reg_counter++;
                       out.println("\tbr i1 %_" + (reg_counter-1) + ", label %while_then_" + while_then_counter + ", label %while_end_" + while_then_counter + "\n");
                }
                else{//an to cond den einai ths synartisis
                       if(expr==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                           out.println("\tbr i1 %_" + (reg_counter-1) + ", label %while_then_" + while_then_counter + ", label %while_end_" + while_then_counter + "\n");
                        }
                       else{
                           map = (HashMap)visitor1.offsets.get(current_class).get(0); 
                           while(map.get(expr)==null){
                                current_class = visitor1.extend_classes.get(current_class);
                                map = (HashMap)visitor1.offsets.get(current_class).get(0);
                            }
                           offset = (int)map.get(expr) +8;
                           out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                           reg_counter++;
                           out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));
                           reg_counter++;
                           out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                           reg_counter++;
                           out.println("\tbr i1 %_" + (reg_counter-1) + ", label %while_then_" + while_then_counter + ", label %while_end_" + while_then_counter + "\n");
                       }
                }
            }
            
            out.println("\twhile_then_" + while_then_counter + ":");
      } catch (IOException e) {
      }
      
      String Stat = n.f4.accept(this, argu);
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            out.println("\tbr label %while_" + while_then_counter + "\n");
            out.println("\twhile_end_" + while_then_counter + ":");
      } catch (IOException e) {
      }
      while_counter++;
      return _ret;
   }
   
   
   public String visit(PrintStatement n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      value_flag = "right";
      first_reg = sec_reg = -1;
       
      String expr = n.f2.accept(this, argu);
    
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String Nclass;
            HashMap map;
            int offset;
            try {
                 Integer.parseInt(expr);
                 out.println("\tcall void (i32) @print_int(i32  " + expr + ")");
            }  
            catch (NumberFormatException e)
            {
                  Nclass = Var_of_Function(visitor1,expr,"int");          //Nclass is the class thas has as field the expr
                  if(Nclass == null){ //an to expr ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + expr); 
                       out.println("\tcall void (i32) @print_int(i32  %_" + reg_counter + ")" );
                       reg_counter++;
                   }
                   else{//an to expr den einai ths synartisis
                      if(expr==null){
                          out.println("\tcall void (i32) @print_int(i32  %_" + (reg_counter-1) + ")");
                      }
                      else{
                         map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                         while(map.get(expr)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                         }
                         offset = (int)map.get(expr) +8;
                         out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                         reg_counter++;
                         out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                         reg_counter++;
                         out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                         out.println("\tcall void (i32) @print_int(i32  %_" + reg_counter + ")");
                         reg_counter++;
                      }
                  }
            }
      } catch (IOException e) {
        }
      
      first_reg = sec_reg = -1;
      return _ret;
   }
   
   
   public String visit(AndExpression n, GJDepthFirst argu) {
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
     value_flag = "right";
      exp_res_counter+=4;
      int exp_counter= exp_res_counter;
      
      String first = n.f0.accept(this, argu);
    
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          if (first == "true"  ){
                  out.println("\t%_" + reg_counter + " = alloca i8");
                  out.println("\tstore i8 1, i8* %_"+ reg_counter );
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));  
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                  reg_counter++;
          }
          else if(first=="false"){
                  out.println("\t%_" + reg_counter + " = alloca i8");
                  out.println("\tstore i8 0, i8* %_"+ reg_counter );
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));     
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                  reg_counter++;
          }
          else if(first!=null){
                 Nclass = Var_of_Function(visitor1,first,"boolean");          //Nclass is the class thas has as field the first
                 if(Nclass == null){ //an to first ths synartisis
                       out.println("\t%_" + reg_counter + " = load i8, i8* %" + first);     
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                       reg_counter++;
                    }
                    else{   //an to first den einai ths synartisis
                       map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                       while(map.get(first)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                         }
                       offset = (int)map.get(first) +8;
                       out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                       reg_counter++;
                  }
                 
             }
            out.println("\tbr i1 %_" + (reg_counter-1) + ", label %exp_res_" + (exp_counter+1) + ", label %exp_res_" + exp_counter+ "\n");
            out.println("\texp_res_" + exp_counter + ":");
            out.println("\tbr label %exp_res_" + (exp_counter+3) + "\n");
            out.println("\texp_res_" + (exp_counter+1) + ":");
      }
         catch (IOException e) {
        }
         
      String second = n.f2.accept(this, argu);
     
  
      try(FileWriter fw = new FileWriter(visitor1.FileName, true); 
      BufferedWriter bw = new BufferedWriter(fw);
      PrintWriter out = new PrintWriter(bw)){
          String Nclass;
          HashMap map;
          int offset;
          
          if (second == "true"  ){
                  out.println("\t%_" + reg_counter + " = alloca i8");
                  out.println("\tstore i8 1, i8* %_"+ reg_counter );
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));  
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                  reg_counter++;
          }
          else if(second=="false"){
                  out.println("\t%_" + reg_counter + " = alloca i8");
                  out.println("\tstore i8 0, i8* %_"+ reg_counter );
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));     
                  reg_counter++;
                  out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                  reg_counter++;
          }
          else if(second!=null){
                 Nclass = Var_of_Function(visitor1,second,"boolean");          //Nclass is the class thas has as field the second
                 if(Nclass == null){ //an to first ths synartisis
                       out.println("\t%_" + reg_counter + " = load i8, i8* %" + second);     
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                       reg_counter++;
                    }
                    else{   //an to first den einai ths synartisis
                       map = (HashMap)visitor1.offsets.get(Nclass).get(0);  
                       while(map.get(second)==null){
                                Nclass = visitor1.extend_classes.get(Nclass);
                                map = (HashMap)visitor1.offsets.get(Nclass).get(0);
                         }
                       offset = (int)map.get(second) +8;
                       out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                       reg_counter++;
                  }
                
             }
                out.println("\tbr label %exp_res_" + (exp_counter+2) +"\n");
                out.println("\texp_res_" + (exp_counter+2) +":");
                out.println("\tbr label %exp_res_" + (exp_counter+3) +"\n");
                out.println("\texp_res_" + (exp_counter+3) +":");
                out.println("\t%_" + reg_counter + " = phi i1  [ 0, %exp_res_" + exp_counter + " ], [ %_" + (reg_counter-1) + ", %exp_res_" + (exp_counter+2) + " ]\n");
                reg_counter++;
      }
         catch (IOException e) {
        }
      exp_res_counter = exp_res_counter+4;
      if(first_reg==-1 || (first_reg!=-1 && sec_reg != -1))
          first_reg = reg_counter-1;
      else
          sec_reg = reg_counter-1;
      
      return _ret;
   }
   
  public String Var_of_Function(DefCollectVisitor visitor,String var, String type){
           String current_class = classname;
            if(var==null)
                return "NO";
           if(method_vars!=null && method_vars.get(var)==type)       //an einai metabliti orismeni mesa sthn synartisi
               return null;
           ListIterator<List> Tableitr;
           ListIterator  listitr=null;
           Object extend_vars =  null,fun_vars=null, class_vars=null;
           String var_type=null;

      while(current_class!=null){
           Tableitr=visitor.SymbolTable.listIterator();
           while(Tableitr.hasNext()) {

                      listitr=Tableitr.next().listIterator();
                      while(listitr.hasNext()) {

                             HashMap next_map = (HashMap)listitr.next();
                             extend_vars = next_map.get(current_class);                  //class
                             if(extend_vars !=null){
                                  if(current_class == visitor.Mainclass){       //an eimaste sthn Main class tote mono pedio ths synartisis main mporei na einai
                                      var_type = (String)((HashMap)extend_vars).get(var);
                                        if(var_type==type)
                                            return null;
                                  }
                                  class_vars  = extend_vars;
                                 while(listitr.hasNext()) {
                                    next_map = (HashMap)listitr.next();
                                    
                                    fun_vars = next_map.get(functionname);                  //elegxoume an einai kapoio argument synartisis
                                    if(fun_vars!=null){
                                        var_type = (String)((HashMap)fun_vars).get(var);
                                        if(var_type==type)
                                            return null;
                                        else
                                            break;
                                    }
                                }
                            }
                      }
           }
           if(class_vars!=null){                //elegxoume mipws einai metabliti tis klasis 
                var_type = (String)((HashMap)class_vars).get(var);
                 if(var_type==type)
                        return current_class;
           }
           class_vars=null;
           current_class = visitor.extend_classes.get(current_class);
        }
           return null;
  }
   
   public String visit(AssignmentStatement n, GJDepthFirst argu) {
       newAlloc_flag = false;
       
       DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
    
      boolean accept_flag=false;
      String _ret=null;
      value_flag = "left";
      String id = n.f0.accept(this, argu);
      String id_type = type1;
      int id_reg=-1, expr_reg=-1;
      
      // h periptwsi poy to id einai pedio ths synartisis
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String current_class;
            HashMap map;
            int offset;
            String to_class = Var_of_Function(visitor1,id,id_type);
            if(to_class == null ){
                id_reg = -1; //simainei to idio to onoma tis metablitis
            }
            else{           //an to id den einai pedio ths synartisis
                if(id!=null){
                     map = (HashMap)visitor1.offsets.get(to_class).get(0);
                     while(map.get(id)==null){
                            to_class = visitor1.extend_classes.get(to_class);
                            map = (HashMap)visitor1.offsets.get(to_class).get(0);
                      }
                     offset = (int)map.get(id) +8;
                     out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                     reg_counter++;
                }
                id_reg = reg_counter-1;
            }
      } catch (IOException e) {
        }
      
      
      value_flag="right";
      String expr = n.f2.accept(this, argu);
      HashMap map;
      if(type1 != id_type){
          String cur_classname = type1;
           
           while((cur_classname = visitor1.extend_classes.get(cur_classname)) !=null){
                       if(cur_classname == id_type){
                           accept_flag=true;
                           break;
                       }
           }
      }
      
      // h periptwsi poy to id einai pedio ths synartisis
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String current_class;
            int offset;
            if(id_reg == -1 ){ //an to id ths synartisis
                
                    if(expr=="true")
                        out.println("\tstore " + FindType(type1) + " " + "1, " + FindType(id_type) + "* %" + id );
                    else if(expr=="false")
                        out.println("\tstore " + FindType(type1) + " " + "0, " + FindType(id_type) + "* %" + id );
                    else if(id_type=="boolean"){
                        current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                        if(current_class == null){ //an to expr ths synartisis
                            out.println("\t%_" + reg_counter + " = load i8, i8* %" + expr);
                            reg_counter++;
                            out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                            reg_counter++;
                            out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                            out.println("\tstore i8 %_" + reg_counter + ", i8* %" + id);
                            reg_counter++;
                        }
                        else{//an to expr den einai ths synartisis
                            if(expr==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                                    out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                                    out.println("\tstore i8 %_" + reg_counter + ", i8* %" + id);
                                    reg_counter++;
                             }
                            else{
                                map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                while(map.get(expr)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                 }
                                offset = (int)map.get(expr) +8;
                                out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                                out.println("\tstore i8 %_" + reg_counter + ", i8* %" + id);
                                reg_counter++;
                            }
                        }
                    }
                    else if(id_type =="boolean[]"){
                        if(expr==null)
                            out.println("\tstore i8* %_" + bool_array_reg +", i8** %" + id);  
                        else{
                            current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                            if(current_class == null){ //an to expr ths synartisis
                                out.println("\t%_" + reg_counter + " = load i8*, i8** %" + expr);     
                                out.println("\tstore i8* %_" + reg_counter + ", i8** %" + id);
                                reg_counter++;
                            }
                            else{
                                map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                while(map.get(expr)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                 }
                                offset = (int)map.get(expr) +8;
                                out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);        
                                out.println("\tstore i8* %_" + (reg_counter) + ", i8** %" + id);
                                reg_counter++;
                            }
                        }
                    }
                    else if(id_type=="int"){
                        try { 
                            Integer.parseInt(expr);
                            out.println("\tstore " + FindType(type1) + " " + expr + ", " + FindType(id_type) + "* %" + id );
                        }  
                        catch (NumberFormatException e)
                        {
                            //elegxos gia to an h metabliti expr einai pedio tis sinartisis i kapoias klasis
                            current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                            if(current_class == null){ //an to expr ths synartisis

                                out.println("\t%_" + reg_counter + " = load i32, i32* %" + expr);     
                                out.println("\tstore i32 %_" + reg_counter + ", i32* %" + id);
                                reg_counter++;
                            }
                            else{//an to expr den einai ths synartisis
                                if(expr==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                                    out.println("\tstore i32 %_" + (reg_counter-1) + ", i32* %" + id);
                                }
                                else{
                                    map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                    while(map.get(expr)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                    }
                                    offset = (int)map.get(expr) +8;
                                    out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                                    out.println("\tstore i32 %_" + (reg_counter) + ", i32* %" + id);
                                    reg_counter++;
                                }
                            }
                        }

                    }
                    else if(id_type =="int[]"){
                        if(expr==null)
                            out.println("\tstore i32* %_" + (reg_counter-1) +", i32** %" + id);  
                        else{
                            current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                            if(current_class == null){ //an to expr ths synartisis
                                out.println("\t%_" + reg_counter + " = load i32*, i32** %" + expr);     
                                out.println("\tstore i32* %_" + reg_counter + ", i32** %" + id);
                                reg_counter++;
                            }
                            else{
                                map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                while(map.get(expr)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                 }
                                offset = (int)map.get(expr) +8;
                                out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                reg_counter++;
                                out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32**");
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = load i32*, i32** %_" + (reg_counter-1));
                                out.println("\tstore i32* %_" + (reg_counter) + ", i32** %" + id);
                                reg_counter++;
                            }
                        }
                    }
                    else{
                        if (newAlloc_flag==true)
                            out.println("\tstore i8* %_" + (reg_counter-3) + ", i8** %" + id );
                        else if(expr==classname){       //this
                            out.println("\tstore i8* %this, i8** %" + id);
                        }
                        else{
                            current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                            if(current_class == null){ //an to expr ths synartisis
                                out.println("\t%_" + reg_counter + " = load i8*, i8** %" + expr);  
                                out.println("\tstore i8* %_" + reg_counter + ", i8** %" + id);
                                reg_counter++;
                            }
                            else{   //an to expr den einai ths synartisis
                                if(expr==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                                    out.println("\tstore i8* %_" + (reg_counter-1) + ", i8** %" + id);
                                }
                                else{
                                    map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                    while(map.get(expr)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                    }
                                    offset = (int)map.get(expr) +8;
                                    out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i8**"); //to bitcast kai to load den einai sigouro
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load i8*, i8** %_" + (reg_counter-1));
                                    out.println("\tstore i8* %_" + reg_counter + ", i8** %" + id);
                                    reg_counter++;
                                }
                            }
                                
                        }
                        newAlloc_flag=false;
                    }
            }
            else{           //an to id den einai pedio ths synartisis
                     
                     if(expr=="true"){
             
                        out.println("\tstore " + FindType(type1) + " " + "1, " + FindType(id_type) + "* %_" + id_reg );
                     }
                    else if(expr=="false"){
          
                        out.println("\tstore " + FindType(type1) + " " + "0, " + FindType(id_type) + "* %_" + id_reg );
                    }
                    else if(id_type=="boolean"){
                        
                        current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                        if(current_class == null){ //an to expr ths synartisis
                            out.println("\t%_" + reg_counter + " = load i8, i8* %" + expr);
                            reg_counter++;
                            out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                            reg_counter++;
                            out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                            out.println("\tstore i8 %_" + reg_counter + ", i8* %_" + id_reg);
                            reg_counter++;
                            
                        }
                        else{//an to expr den einai ths synartisis
                            if(expr==null){
                                out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                                out.println("\tstore i8 %_" + reg_counter + ", i8* %_" +  id_reg);
                                reg_counter++;
                            }
                            else{
                                map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                while(map.get(expr)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                 }
                                offset = (int)map.get(expr) +8;
                                out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                                out.println("\tstore i8 %_" + reg_counter + ", i8* %_" +  id_reg);
                                reg_counter++;
                            }
                               
                        }
                    }
                    else if(id_type =="boolean[]"){
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + id_reg + " to i8**");
                        id_reg = reg_counter;
                        reg_counter++;
                        if(expr==null)
                            out.println("\tstore i8* %_" + bool_array_reg +", i8** %_" + id_reg);  
                        else{
                            current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                            if(current_class == null){ //an to expr ths synartisis
                                out.println("\t%_" + reg_counter + " = load i8*, i8** %" + expr);     
                                out.println("\tstore i8* %_" + reg_counter + ", i8** %_" + id_reg);
                                reg_counter++;
                            }
                            else{
                                map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                while(map.get(expr)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                 }
                                offset = (int)map.get(expr) +8;
                                out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);     
                                out.println("\tstore i8* %_" + (reg_counter) + ", i8** %_" + id_reg);
                                reg_counter++;
                            }
                        }
                    }
                    else if(id_type=="int"){
                        try { 
                            Integer.parseInt(expr);
                            out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + id_reg + " to i32*");
                            id_reg = reg_counter;
                            out.println("\tstore " + FindType(type1) + " " + expr + ", " + FindType(id_type) + "* %_" + id_reg );
                            reg_counter++;
                        }
                        catch (NumberFormatException e)
                        {
                            //elegxos gia to an h metabliti expr einai pedio tis sinartisis i kapoias klasis
                            current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                            if(current_class == null){ //an to expr ths synartisis
                                out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + id_reg + " to i32*");
                                id_reg = reg_counter;
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = load i32, i32* %" + expr);     
                                out.println("\tstore i32 %_" + reg_counter + ", i32* %_" + id_reg);
                                reg_counter++;
                            }
                            else{//an to expr den einai ths synartisis
                                out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + id_reg + " to i32*");
                                id_reg = reg_counter;
                                reg_counter++;
                                if(expr==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                                    out.println("\tstore i32 %_" + (reg_counter-2) + ", i32* %_" + id_reg);
                                }
                                else{
                                    map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                    while(map.get(expr)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                    }
                                    offset = (int)map.get(expr) +8;
                                    out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                                    out.println("\tstore i32 %_" + (reg_counter) + ", i32* %_" + id_reg);
                                    reg_counter++;
                                }
                            }
                        }
                    }
                    else if(id_type =="int[]"){
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + id_reg + " to i32**");
                        id_reg = reg_counter;
                        reg_counter++;
                        if(expr==null)
                            out.println("\tstore i32* %_" + (reg_counter-2) +", i32** %_" +  id_reg);  
                        else{
                            current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                            if(current_class == null){ //an to expr ths synartisis
                                out.println("\t%_" + reg_counter + " = load i32*, i32** %" + expr);     
                                out.println("\tstore i32* %_" + reg_counter + ", i32** %_" +  id_reg);
                                reg_counter++;
                            }
                            else{
                                map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                while(map.get(expr)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                 }
                                offset = (int)map.get(expr) +8;
                                out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                reg_counter++;
                                out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32**");
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = load i32*, i32** %_" + (reg_counter-1));
                                out.println("\tstore i32* %_" + (reg_counter) + ", i32** %_" +  id_reg);
                                reg_counter++;
                            }
                        }
                    }
                     else{
                        if (newAlloc_flag==true){
                            out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + id_reg + " to i8**");         
                            id_reg = reg_counter;
                            reg_counter++;
                            out.println("\tstore i8* %_" + (alloc_reg_counter-3) + ", i8** %_" + id_reg );
                        }
                        else if(expr==classname){
                            out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + id_reg + " to i8**");         
                            id_reg = reg_counter;
                            reg_counter++;
                            out.println("\tstore i8* %this, i8** %_" + id_reg );
                        }
                        else{
                            current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                            if(current_class == null){ //an to expr ths synartisis
                                out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + id_reg + " to i8**");         
                                id_reg = reg_counter;
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = load i8*, i8** %" + expr);   //an to expr ths synartisis
                                out.println("\tstore i8* %_" + reg_counter + ", i8** %_" + id_reg);
                                reg_counter++;
                            }
                            else{//an to expr den einai ths synartisis
                                 out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + id_reg + " to i8**");         
                                 id_reg = reg_counter;
                                 reg_counter++;
                                 if(expr==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                                    out.println("\tstore i8* %_" + (reg_counter-2) + ", i8** %_" + id_reg);
                                }
                                else{
                                    map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                    while(map.get(expr)==null){
                                        current_class = visitor1.extend_classes.get(current_class);
                                        map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                    }
                                    offset = (int)map.get(expr) +8;
                                    out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i8**");
                                    reg_counter++;
                                    out.println("\t%_" + reg_counter + " = load i8*, i8** %_" + (reg_counter-1));
                                    out.println("\tstore i8* %_" + reg_counter + ", i8** %_" + id_reg);
                                    reg_counter++;
                                 }
                            }
                        }
                        newAlloc_flag=false;
                    }
            }
      } catch (IOException e) {
            //exception handling left as an exercise for the reader
        }
      
      bool_array_reg =-1;
      if(first_reg==-1 || (first_reg!=-1 && sec_reg != -1))
          first_reg = reg_counter-1;
      else
          sec_reg = reg_counter-1;
      
      return _ret;
   }

   
   public String visit(ArrayAssignmentStatement n, GJDepthFirst argu) {
   
      DefCollectVisitor visitor1 = (DefCollectVisitor)argu;
      String _ret=null;
      value_flag = "left";
      String id =n.f0.accept(this, argu);
      String id_type = type1;
      int array_reg=-1, size_reg=-1,index_reg=-1,array_position=-1;
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String current_class;
            int offset;
            HashMap map;
            String to_class = Var_of_Function(visitor1,id,id_type);
            if(id_type=="int[]"){
         // h periptwsi poy to id einai pedio ths synartisis
       
                if(to_class == null){ //an to id ths synartisis
                    out.println("\t%_" + reg_counter + " = load i32*, i32** %" + id);
                    array_reg = reg_counter;
                    reg_counter++;
                    out.println("\t%_" + reg_counter + " = load i32, i32* %_" + array_reg);     //fortwnw to size toy array (1o stoixeio toy pinaka)
                    size_reg = reg_counter;
                    reg_counter++;
                }
                else{
                    if(id==null){
                        array_reg = reg_counter-1;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + array_reg);     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        size_reg = reg_counter;
                        reg_counter++;
                    }
                    else{
                        map = (HashMap)visitor1.offsets.get(to_class).get(0);
                        while(map.get(id)==null){
                              to_class = visitor1.extend_classes.get(to_class);
                              map = (HashMap)visitor1.offsets.get(to_class).get(0);
                        }
                        offset = (int)map.get(id) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32**");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32*, i32** %_" + (reg_counter-1));
                        array_reg = reg_counter;
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + array_reg);     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        size_reg = reg_counter;
                        reg_counter++;
                    }
                }
            }
            else if (id_type=="boolean[]"){
                if(to_class == null){ //an to id ths synartisis
                    out.println("\t%_" + reg_counter + " = load i8*, i8** %" + id);
                    array_reg = reg_counter;
                    reg_counter++;
                    out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                    reg_counter++;
                    out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1) );     //fortwnw to size toy array (1o stoixeio toy pinaka)
                    size_reg = reg_counter;
                    reg_counter++;
                }
                else{
                    if(id==null){
                        array_reg = reg_counter-1;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        size_reg = reg_counter;
                        reg_counter++;
                    }
                    else{
                        map = (HashMap)visitor1.offsets.get(to_class).get(0);
                        while(map.get(id)==null){
                              to_class = visitor1.extend_classes.get(to_class);
                              map = (HashMap)visitor1.offsets.get(to_class).get(0);
                        }
                        offset = (int)map.get(id) +8;
                        out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                        array_reg = reg_counter;
                        reg_counter++;
                        out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                        reg_counter++;
                        out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));     //fortwnw to size toy array (1o stoixeio toy pinaka)
                        size_reg = reg_counter;
                        reg_counter++;
                    }
                }
            }
       }catch (IOException e) {
        }
      
      String index = n.f2.accept(this, argu);
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String current_class;
            int offset;
            HashMap map;
            try { 
                 Integer.parseInt(index);
                 out.println("\t%_" + reg_counter + " = icmp sge i32 "+ index + ", 0");  //index >=0
                 reg_counter++;
                 out.println("\t%_" + reg_counter + " = icmp slt i32 " + index + ", %_" + size_reg); //index < size_array
                 reg_counter++;
            }
            catch (NumberFormatException e)
           {
                  //elegxos gia to an h metabliti index einai pedio tis sinartisis i kapoias klasis
                  current_class = Var_of_Function(visitor1,index,"int");          //currentclass is the class thas has as field the index
                  if(current_class == null){ //an to expr ths synartisis

                       out.println("\t%_" + reg_counter + " = load i32, i32* %" + index);
                       index_reg = reg_counter;
                      reg_counter++;
                       out.println("\t%_" + reg_counter + " = icmp sge i32 %_"+ index_reg + ", 0");  //index >=0
                       reg_counter++;
                       out.println("\t%_" + reg_counter + " = icmp slt i32 %_" + index_reg + ", %_" + size_reg); //index < size_array
                       reg_counter++;
                   }
                   else{//an to index den einai ths synartisis
                       if(index==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                              index_reg = reg_counter - 1;
                              out.println("\t%_" + reg_counter + " = icmp sge i32 %_"+ index_reg + ", 0");  //index >=0
                              reg_counter++;
                              out.println("\t%_" + reg_counter + " = icmp slt i32 %_" + index_reg + ", %_" + size_reg); //index < size_array
                              reg_counter++;
                       }
                      else{
                              map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                              while(map.get(index)==null){
                                    current_class = visitor1.extend_classes.get(current_class);
                                    map = (HashMap)visitor1.offsets.get(current_class).get(0);
                              }
                              offset = (int)map.get(index) +8;
                              out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                              reg_counter++;
                              out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                              reg_counter++;
                              out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                              index_reg = reg_counter;
                              reg_counter++;
                              out.println("\t%_" + reg_counter + " = icmp sge i32 %_"+ index_reg + ", 0");  //index >=0
                              reg_counter++;
                              out.println("\t%_" + reg_counter + " = icmp slt i32 %_" + index_reg + ", %_" + size_reg); //index < size_array
                              reg_counter++;
                      }
                  }
              }
            oob_counter++;
            out.println("\t%_" + reg_counter + " = and i1 %_" + (reg_counter-1) + ", %_" + (reg_counter-2));    //na isxyoun kai oi 2 periorismoi
            out.println("\tbr i1 %_" + reg_counter + ", label %oob_ok_" + oob_counter+ ", label %oob_err_" + oob_counter);
            reg_counter++;
            out.println("\n\toob_err_" + oob_counter + ":");
            out.println("\tcall void @throw_oob()");
            out.println("\tbr label %oob_ok_" + oob_counter);
            out.println("\n\toob_ok_" + oob_counter + ":");
            oob_counter ++;
            if (id_type=="int[]"){
                try {                                                       //prosthetw 1 sto index giati sthn 1h thesi einai to size
                     Integer.parseInt(index);
                     out.println("\t%_" + reg_counter + " = add i32 1, " + index);
                     reg_counter++;
                }
                catch (NumberFormatException e)
               {
                   out.println("\t%_" + reg_counter + " = add i32 1, %_" + index_reg);
                   reg_counter++;
               }

                out.println("\t%_" + reg_counter +" = getelementptr i32, i32* %_" + array_reg + ", i32 %_" + (reg_counter-1));
                array_position = reg_counter;
                reg_counter++;
            }
            else if (id_type=="boolean[]"){
                try {                                                       //prosthetw 1 sto index giati sthn 1h thesi einai to size
                     Integer.parseInt(index);
                     out.println("\t%_" + reg_counter + " = add i32 4, " + index);
                     reg_counter++;
                }
                catch (NumberFormatException e)
               {
                   out.println("\t%_" + reg_counter + " = add i32 4, %_" + index_reg);
                   reg_counter++;
               }

                out.println("\t%_" + reg_counter +" = getelementptr i8, i8* %_" + array_reg + ", i32 %_" + (reg_counter-1));
                array_position = reg_counter;
                reg_counter++;
            }
            
        } catch (IOException e) {
        }
      
      value_flag = "right";
      String expr = n.f5.accept(this, argu);
      
      try(FileWriter fw = new FileWriter(visitor1.FileName, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw)){
            String current_class;
            int offset;
            HashMap map;
            if(id_type=="int[]"){
                try { 
                     Integer.parseInt(expr);
                     out.println("\tstore i32 " + expr + ", i32* %_" + array_position);
                }
                catch (NumberFormatException e)
               {
                      //elegxos gia to an h metabliti expr einai pedio tis sinartisis i kapoias klasis
                      current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                      if(current_class == null){ //an to expr ths synartisis

                           out.println("\t%_" + reg_counter + " = load i32, i32* %" + expr);
                           reg_counter++;
                           out.println("\tstore i32 %_" + (reg_counter-1) + ", i32* %_" + array_position);
                       }
                       else{//an to expr den einai ths synartisis
                           if(expr==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                                  out.println("\tstore i32 %_" + (reg_counter-1) + ", i32* %_" + array_position);
                           }
                          else{
                                  map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                  while(map.get(expr)==null){
                                    current_class = visitor1.extend_classes.get(current_class);
                                    map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                  }
                                  offset = (int)map.get(expr) +8;
                                  out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                  reg_counter++;
                                  out.println("\t%_" + reg_counter +" = bitcast i8* %_"  + (reg_counter-1) + " to i32*");
                                  reg_counter++;
                                  out.println("\t%_" + reg_counter + " = load i32, i32* %_" + (reg_counter-1));
                                  reg_counter++;
                                  out.println("\tstore i32 %_" + (reg_counter-1) + ", i32* %_" + array_position);
                          }
                      }
                  }
            }
            else if(id_type=="boolean[]"){
                if(expr=="true"){
                        out.println("\t%_" + reg_counter + " = zext i1 1 to i8");
                        out.println("\tstore i8 %_"+ reg_counter + " ,  i8* %_" + array_position );
                        reg_counter++;
                }
                else if(expr=="false"){
                        out.println("\t%_" + reg_counter + " = zext i1 0 to i8");
                        out.println("\tstore i8 %_"+ reg_counter + " ,  i8* %_" + array_position );
                        reg_counter++;
                }
                else{
                    current_class = Var_of_Function(visitor1,expr,id_type);          //currentclass is the class thas has as field the expr
                    if (current_class == null){ //an to expr ths synartisis
                            out.println("\t%_" + reg_counter + " = load i8, i8* %" + expr);
                            reg_counter++;
                            out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                            reg_counter++;
                            out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                            out.println("\tstore i8 %_" + reg_counter + ", i8* %_" + array_position);
                            reg_counter++;
                        }
                    else{//an to expr den einai ths synartisis
                            if(expr==null){      // shmainei oti exei prokypsei apo kapoio syntheto expression px plus/minus
                                    out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                                    out.println("\tstore i8 %_" + reg_counter + ", i8* %_" + array_position);
                                    reg_counter++;
                             }
                            else{
                                map = (HashMap)visitor1.offsets.get(current_class).get(0);  
                                while(map.get(expr)==null){
                                    current_class = visitor1.extend_classes.get(current_class);
                                    map = (HashMap)visitor1.offsets.get(current_class).get(0);
                                }
                                offset = (int)map.get(expr) +8;
                                out.println("\t%_" + reg_counter + " = getelementptr i8, i8* %this, i32 " + offset);
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = load i8, i8* %_" + (reg_counter-1));
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = trunc i8 %_" + (reg_counter-1) + " to i1");
                                reg_counter++;
                                out.println("\t%_" + reg_counter + " = zext i1 %_" + (reg_counter-1) + " to i8");
                                out.println("\tstore i8 %_" + reg_counter + ", i8* %_" + array_position);
                                reg_counter++;
                            }
                        }
                }
            }
      }catch (IOException e) {
        }
      
      if(id_type == "int[]")
          id_type = "int";
      else if(id_type == "boolean[]")
          id_type = "boolean";
   
      return _ret;
   }
   
    public String visit(PrimaryExpression n, GJDepthFirst argu) {
      String exp= n.f0.accept(this, argu);
      if(exp == "this"){
          exp = classname;
          type1 = classname;
      }
      return exp;
   }
    
    
   public String visit(BracketExpression n, GJDepthFirst argu) {
      String _ret=null;
      n.f0.accept(this, argu);
     
      String exp = n.f1.accept(this, argu);
      n.f2.accept(this, argu);
     
      return exp;
   }
}