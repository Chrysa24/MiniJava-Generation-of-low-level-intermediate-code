import syntaxtree.*;
import visitor.*;
import java.io.*;
import java.io.File;  // Import the File class
import java.io.FileWriter;   // Import the FileWriter class
import java.io.IOException;  // Import the IOException class to handle errors


public class Main {
   
    public static void main (String [] args){
    if(args.length == 0){
        System.err.println("Usage: java Main <inputFile>");
        System.exit(1);
    }
    FileInputStream fis = null;
    
    try{
        int counter=1;
        for (String arg: args) {
            System.out.println("\nInput file" + counter + ": "  + arg + "\n");
            counter ++;
            



            fis = new FileInputStream(arg);
            MiniJavaParser parser = new MiniJavaParser(fis);
            Goal root = parser.Goal();
            DefCollectVisitor visitor1 = new DefCollectVisitor();

            root.accept(visitor1, arg.substring(0, arg.length()-5)+".ll");
            Third_Part_Visitor visitor2 = new Third_Part_Visitor();
            fis = new FileInputStream(arg);

            parser = new MiniJavaParser(fis);
            root = parser.Goal();
            root.accept(visitor2, visitor1);
            System.out.println("File: " +  arg.substring(0, arg.length()-5)+".ll just created");
        }
       
    }
    catch(ParseException ex){
        System.out.println(ex.getMessage());
    }
    catch(FileNotFoundException ex){
        System.err.println(ex.getMessage());
    }
    finally{
        try{
        if(fis != null) fis.close();
        }
        catch(IOException ex){
        System.err.println(ex.getMessage());
        }
    }
    }
}
