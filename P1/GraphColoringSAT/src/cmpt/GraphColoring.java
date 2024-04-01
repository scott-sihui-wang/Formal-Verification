package cmpt;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Scanner;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

public class GraphColoring {
    public static void main(String[] args) throws FileNotFoundException, IOException {
        File file=new File("./src/cmpt/input.txt");
        Scanner in=new Scanner(file);
        Context ctx=new Context();
        Solver solver=ctx.mkSolver();
        String data[]=in.nextLine().split(" ");
        int num_vertex=Integer.parseInt(data[0]);
        int num_color=Integer.parseInt(data[1]);
        BoolExpr[][]p=new BoolExpr[num_vertex][num_color];
        for (int i = 0; i < num_vertex; ++i) {
            for (int j = 0; j < num_color; ++j) {
                p[i][j] = ctx.mkBoolConst("p_" + i + "_" + j);
            }
        }
        for(int i=0;i<num_vertex;i++){
            solver.add(ctx.mkOr(p[i]));
            for(int j=0;j<num_color-1;j++){
                for(int k=j+1;k<num_color;k++){
                    solver.add(ctx.mkOr(ctx.mkNot(p[i][j]),ctx.mkNot(p[i][k])));
                }
            }
        }
        while (in.hasNextLine()){
            String edge[]=in.nextLine().split(" ");
            int num_1=Integer.parseInt(edge[0]);
            int num_2=Integer.parseInt(edge[1]);
            for(int i=0;i<num_color;i++){
                solver.add(ctx.mkOr(ctx.mkNot(p[num_1-1][i]),ctx.mkNot(p[num_2-1][i])));
            }
        }
        Status status = solver.check();
        System.out.println(status);
        File out=new File("./src/cmpt/output.txt");
        FileWriter writer=new FileWriter(out);
        if(status.toString().equals("SATISFIABLE")){
            Model model = solver.getModel();
            for(int i=0;i<num_vertex;i++){
                for(int j=0;j<num_color;j++){
                    if(model.getConstInterp(p[i][j]).toString().equals("true")){
                        writer.write(Integer.toString(i+1));
                        writer.write(" ");
                        writer.write(Integer.toString(j+1));
                        writer.write("\n");
                    }
                }
            }
        }
        else if(status.toString().equals("UNSATISFIABLE")){
            writer.write("UNSAT");
            writer.write("\n");
        }
        in.close();
        writer.close();
    }
}