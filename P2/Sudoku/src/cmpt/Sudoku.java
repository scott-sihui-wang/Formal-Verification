package cmpt;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Scanner;

import com.microsoft.z3.*;

public class Sudoku {
    public static void main(String[] args) throws FileNotFoundException, IOException {
        Context ctx=new Context();
        Solver solver=ctx.mkSolver();
        IntExpr[][] p=new IntExpr[9][9];
        for(int i=0;i<9;i++){
            for(int j=0;j<9;j++){
                p[i][j]=ctx.mkIntConst("p_"+i+"_"+j);
                solver.add(ctx.mkAnd(ctx.mkLe(ctx.mkInt(1),p[i][j]),ctx.mkLe(p[i][j],ctx.mkInt(9))));
            }
        }
        File inFile=new File("./src/cmpt/input.txt");
        Scanner in=new Scanner(inFile);
        for(int i=0;i<9;i++) {
            solver.add(ctx.mkDistinct(p[i]));
            solver.add(ctx.mkDistinct(p[0][i],p[1][i],p[2][i],p[3][i],p[4][i],p[5][i],p[6][i],p[7][i],p[8][i]));
            solver.add(ctx.mkDistinct(p[(i/3)*3][(i%3)*3],p[(i/3)*3][(i%3)*3+1],p[(i/3)*3][(i%3)*3+2],p[(i/3)*3+1][(i%3)*3],p[(i/3)*3+1][(i%3)*3+1],p[(i/3)*3+1][(i%3)*3+2],p[(i/3)*3+2][(i%3)*3],p[(i/3)*3+2][(i%3)*3+1],p[(i/3)*3+2][(i%3)*3+2]));
            String line[]=in.nextLine().split(" ");
            for(int j=0;j<9;j++){
                int val=Integer.parseInt(line[j]);
                if(val!=0){
                    solver.add(ctx.mkEq(p[i][j],ctx.mkInt(val)));
                }
            }
        }
        Status status=solver.check();
        System.out.println(status);
        File outFile=new File("./src/cmpt/output.txt");
        FileWriter out=new FileWriter(outFile);
        if(status.toString().equals("SATISFIABLE")){
            Model model = solver.getModel();
            for(int i=0;i<9;i++){
                for(int j=0;j<9;j++){
                    out.write(model.getConstInterp(p[i][j]).toString());
                    out.write(" ");
                }
                out.write("\n");
            }
        }
        else if(status.toString().equals("UNSATISFIABLE")){
            out.write("No Solution");
            out.write("\n");
        }
        in.close();
        out.close();
    }
}