package nl.tudelft.instrumentation.symbolic;

import java.io.File;
import java.io.PrintWriter;
import java.nio.file.Path;
import java.util.*;
import com.microsoft.z3.*;
import com.sun.org.apache.xpath.internal.operations.Bool;
import nl.tudelft.instrumentation.fuzzing.DistanceTracker;
import nl.tudelft.instrumentation.fuzzing.FuzzingLab;

import java.util.Random;
import java.io.FileWriter;
import java.io.IOException;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * You should write your solution using this class.
 */
public class SymbolicExecutionLab {
    // Paths
    static String PROBLEM = "problem17";
    static int NUM_RUNS = 0;
    static List<String[]> data = new ArrayList<>();

    // Timer
    static long START_TIME = System.currentTimeMillis();
    static long END_TIME = START_TIME + (60 * 1000 * 15);

    static Random r = new Random();
    static Boolean isFinished = false;
    static List<String> currentTrace;
    static int traceLength = 25;

    static HashSet<String> visitedBranches = new HashSet<>();
    static HashSet<LinkedList<String>> UNSATISFIABLE = new HashSet<>();
    // static PriorityQueue<List<String>> satisfiables = new PriorityQueue<>();
    static HashSet<BoolExpr> unsatisfiables = new HashSet<>();
    static ArrayList<List<String>> satisfiables = new ArrayList<>();
    static HashSet<List<String>> allSatisfiablesRan = new HashSet<>();

    static int branch_counter = 0;

    // Bookkeeping
    static HashSet<String> totalVisitedBranches = new HashSet<>(); // visitedBracnhes of best permutation of all cycles
    static HashSet<String> totalErrorsEncountered = new HashSet<>();

    static void initialize(String[] inputSymbols){
        // Initialise a random trace from the input symbols of the problem.
        currentTrace = generateRandomTrace(inputSymbols);
        System.out.println("RUNNING CURRENT TRACE: " + currentTrace);
    }

    static MyVar createVar(String name, Expr value, Sort s) {
        Context c = PathTracker.ctx;
        /**
         * Create var, assign value and add to path constraint.
         * We show how to do it for creating new symbols, please
         * add similar steps to the functions below in order to
         * obtain a path constraint.
         */
        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        PathTracker.z3model = c.mkAnd(c.mkEq(z3var, value), PathTracker.z3model);
        return new MyVar(z3var, name);
    }

    static MyVar createInput(String name, Expr value, Sort s){
        // Create an input var, these should be free variables!
        Context c = PathTracker.ctx;
        BoolExpr constraint = c.mkFalse();
        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        //        PathTracker.z3model = c.mkAnd(c.mkEq(z3var, value), PathTracker.z3model);

        //
        for (String input: PathTracker.inputSymbols) {
            constraint = c.mkOr(c.mkEq(z3var, c.mkString(input)), constraint);
        }
        PathTracker.z3model = c.mkAnd(constraint, PathTracker.z3model);
        //

        MyVar new_input = new MyVar(z3var, name);
        PathTracker.inputs.add(new_input);

        return new_input;
    }

    static MyVar createBoolExpr(BoolExpr var, String operator){
        // Any unary expression (!)
        Context c = PathTracker.ctx;
        if (operator.equals("!")) {
            return new MyVar(PathTracker.ctx.mkNot(var));
        }
        System.err.println("Unsupported unary operator " + operator);
        return null;
    }

    static MyVar createBoolExpr(BoolExpr left_var, BoolExpr right_var, String operator){
        // Any binary expression (&, &&, |, ||)
        Context c = PathTracker.ctx;
        Expr z3var;
        switch (operator) {
            case "||":
            case "|":
                z3var = c.mkOr(left_var, right_var);
                break;
            case "&&":
            case "&":
                z3var = c.mkAnd(left_var, right_var);
                break;
            default:
                System.err.println("Unsupported boolean operator " + operator);
                z3var =  c.mkFalse();
                break;
        }
        return new MyVar(z3var);
//        return new MyVar(PathTracker.ctx.mkFalse());
    }

    static MyVar createIntExpr(IntExpr var, String operator){
//        if(operator.equals("+") || operator.equals("-"))
//            return new MyVar(PathTracker.ctx.mkInt(0));
//        return new MyVar(PathTracker.ctx.mkFalse());

        Context c = PathTracker.ctx;
        Expr z3var;
        // Any unary expression (+, -)
        switch (operator) {
//            case "+":
//                z3var = var;
//                break;
            case "-":
                z3var = c.mkUnaryMinus(var);
                break;
            default:
                z3var = var;
                break;
        }
        return new MyVar(z3var);
    }

    static MyVar createIntExpr(IntExpr left_var, IntExpr right_var, String operator){
        // Any binary expression (+, -, /, etc)
//        if(operator.equals("+") || operator.equals("-") || operator.equals("/") || operator.equals("*") || operator.equals("%") || operator.equals("^"))
//            return new MyVar(PathTracker.ctx.mkInt(0));
//        return new MyVar(PathTracker.ctx.mkFalse());

        Context c = PathTracker.ctx;
        Expr z3var = null;
        switch (operator) {
            case "+":
                z3var = c.mkAdd(left_var, right_var);
                break;
            case "-":
                z3var = c.mkSub(left_var, right_var);
                break;
            case "/":
                z3var = c.mkDiv(left_var, right_var);
                break;
            case "*":
                z3var = c.mkMul(left_var, right_var);
                break;
            case "%":
                z3var = c.mkMod(left_var, right_var);
                break;
            case "^":
                z3var = c.mkPower(left_var,right_var);
                break;
            case "==":
                z3var = c.mkEq(left_var,right_var);
                break;
            case "<=":
                z3var = c.mkLe(left_var,right_var);
                break;
            case ">=":
                z3var = c.mkGe(left_var,right_var);
                break;
            case ">":
                z3var = c.mkLt(left_var,right_var);
                break;
            case "<":
                z3var = c.mkGt(left_var,right_var);
                break;
            default:
                System.err.println("Unsupported int expression operator " + operator);
                z3var = c.mkFalse();
                break;
        }

        return new MyVar(z3var);
    }

    static MyVar createStringExpr(SeqExpr left_var, SeqExpr right_var, String operator){
        // We only support String.equals
        // return new MyVar(PathTracker.ctx.mkFalse());

        Context c = PathTracker.ctx;
        Expr z3var = c.mkFalse();
        if (operator.equals("==")) {
            z3var = c.mkEq(left_var, right_var);
        }

        return new MyVar(z3var);
    }

    static void assign(MyVar var, String name, Expr value, Sort s){
        // All variable assignments, use single static assignment
        // Check type of value -> assign to new MyVar.
        Context c = PathTracker.ctx;
        var.z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        PathTracker.z3model = c.mkAnd(c.mkEq(var.z3var, value), PathTracker.z3model);
    }

    /**
     * When branch is encountered we want to trigger and solve to opposite side of the branch.
     * Afterward the branches are added to the z3branches.
     *
     *  When you call solve, z3 will try to solve for the inputs considering your current path constraint.
     *  If successful, it will tell you the inputs needed to satisfy the constraint.
     *  You should use this to augment your fuzzer by trying to solve for the opposite side
     *  of the branch you are currently on.
     *
     * @param condition
     * @param value
     * @param line_nr
     */
    static void encounteredNewBranch(MyVar condition, boolean value, int line_nr){
        // Call the solver
        Context c = PathTracker.ctx;
        String branchID = line_nr + "_" + value;

        if(totalVisitedBranches.contains(branchID)) {
            return;
        }

        if(value){
            BoolExpr b_false = c.mkEq(condition.z3var, c.mkBool(false));    // turn false
            if(!unsatisfiables.contains(b_false)) {
                System.out.println("Solving...");
                PathTracker.solve(b_false, false);
                PathTracker.z3branches = c.mkAnd(c.mkEq(condition.z3var, c.mkBool(value)), PathTracker.z3branches);
            } else {
                System.out.println("Already solved...");
            }
        } else {
            BoolExpr b_true = c.mkEq(condition.z3var, c.mkBool(true));      // turn true
            if(!unsatisfiables.contains(b_true)) {
                System.out.println("Solving...");
                PathTracker.solve(b_true, false);
                PathTracker.z3branches = c.mkAnd(c.mkEq(condition.z3var, c.mkBool(value)), PathTracker.z3branches);
            } else {
                System.out.println("Already solved...");
            }
        }

        visitedBranches.add(branchID);
        totalVisitedBranches.add(branchID);
    }

    /**
     * If satisfiable store trace for later processing.
     * Use priority_queue to store and load traces.
     *
     * @param new_inputs
     */
    static void newSatisfiableInput(LinkedList<String> new_inputs) {
        // Hurray! found a new branch using these new inputs!
        LinkedList<String> tmp = new LinkedList<>();
        for(String input : new_inputs){
            tmp.add(input.substring(1, input.length() - 1));
        }

        System.out.println("found satisfiable: " + tmp);
        // Extend trace to explore the branch more
        tmp = extendTrace(tmp);

        System.out.println("Extended to: " + tmp);

        if(!allSatisfiablesRan.contains(tmp)) {
            satisfiables.add(tmp);
        }

        allSatisfiablesRan.add(tmp);
    }

    /**
     * Extends the satisfiable input trace to length of trace_length.
     * This will ensure that satisfiable input are explored a bit deeper.
     * Satisfiable input traces with length > 25 will not be extended anymore
      * @param trace
     * @return
     */
    static LinkedList<String> extendTrace(LinkedList<String> trace) {
        String[] symbols = PathTracker.inputSymbols;
        for(int i = trace.size() - 1; i < traceLength; i++) {
            trace.add(symbols[r.nextInt(symbols.length)]);
        }


        return trace;
    }

    /**
     * If branch was found unsatisfiable by the solver, add to unsatisfiables HashSet to prevent from solving again
      * @param new_branch
     */
    static void addUnsatisfiableInput(BoolExpr new_branch) {
        if(!unsatisfiables.contains(new_branch)) {
            System.out.println("found new unsatisfiable");
            unsatisfiables.add(new_branch);
        }
    }
    /**
     * Method for fuzzing new inputs for a program.
     * @param inputSymbols the inputSymbols to fuzz from.
     * @return a fuzzed sequence
     */
    static List<String> fuzz(String[] inputSymbols){
        /*
         * Add here your code for fuzzing a new sequence for the RERS problem.
         * You can guide your fuzzer to fuzz "smart" input sequences to cover
         * more branches using symbolic execution. Right now we just generate
         * a complete random sequence using the given input symbols. Please
         * change it to your own code.
         */

        // If there are still inputTraces to be run.
        if(!satisfiables.isEmpty()) {
            Random rand = new Random();
            int r = rand.nextInt(satisfiables.size());

            // Try a random input from the satisfiable inputs.
            List<String> next_trace = satisfiables.get(r);
            System.out.println("RUNNING NEXT TRACE: " + next_trace);
            satisfiables.remove(r);
            return next_trace;
        } else { // Try to run a random trace
            PathTracker.reset();
            List<String> rnd = generateRandomTrace(inputSymbols);
            System.out.println("RUNNING RANDOM TRACE: " + rnd);
            return rnd;
        }
    }

    /**
     * Generate a random trace from an array of symbols.
     * @param symbols the symbols from which a trace should be generated from.
     * @return a random trace that is generated from the given symbols.
     */
    static List<String> generateRandomTrace(String[] symbols) {
        ArrayList<String> trace = new ArrayList<>();
        for (int i = 0; i < traceLength; i++) {
            trace.add(symbols[r.nextInt(symbols.length)]);
        }
        return trace;
    }

    static void run() {
        initialize(PathTracker.inputSymbols);
        // Place here your code to guide your fuzzer with its search using Symbolic Execution.
        while(System.currentTimeMillis() < END_TIME) {
            // Do things!
            PathTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));
//
//            try {
//                System.out.println("Woohoo, looping!");
//                Thread.sleep(1000);
//            } catch (InterruptedException e) {
//                e.printStackTrace();
//            }

            System.out.println("Current trace done");
            currentTrace = fuzz(PathTracker.inputSymbols);
            NUM_RUNS++;
            data.add(new String[]{Integer.toString(NUM_RUNS), Integer.toString(totalVisitedBranches.size()), Integer.toString(totalErrorsEncountered.size())});
            PathTracker.reset();
        }

        try {
            writeToCSV();
            writeToFile();
        } catch (IOException e) {
            e.printStackTrace();
        }

        System.out.println("Errors encountered: " + totalErrorsEncountered.size());
        System.out.println("Branches visisted: " + totalVisitedBranches.size());
        System.exit(0);
    }

    static String convertToCSV(String[] data) {
        return Stream.of(data)
                .map(SymbolicExecutionLab::escapeSpecialCharacters)
                .collect(Collectors.joining(","));
    }

    static String escapeSpecialCharacters(String data) {
        String escapedData = data.replaceAll("\\R", " ");
        if (data.contains(",") || data.contains("\"") || data.contains("'")) {
            data = data.replace("\"", "\"\"");
            escapedData = "\"" + data + "\"";
        }
        return escapedData;
    }

    static void writeToCSV() throws IOException {
        File csvOutputFile = new File("docs/lab1/" + PROBLEM + "/problem_graph1.csv");
        try (PrintWriter pw = new PrintWriter(csvOutputFile)) {
            data.stream()
                    .map(SymbolicExecutionLab::convertToCSV)
                    .forEach(pw::println);
        }
    }

    static void writeToFile() {
        try {
            FileWriter myWriter = new FileWriter("docs/lab1/" + PROBLEM + "/problem_errors_Symbolic_Execution.txt", true);
            myWriter.write(PROBLEM + " (" + NUM_RUNS + ")\n\n");

            myWriter.write("Total visited branches: " + totalVisitedBranches.size() + "\n");
            myWriter.write("Total found errors: " + totalErrorsEncountered.size() + "\n");
            myWriter.write("Errors: " + totalErrorsEncountered + "\n");
            myWriter.close();
            System.out.println("Successfully wrote to the file.");
        } catch (IOException e) {
            System.out.println("An error occurred.");
            e.printStackTrace();
        }

    }

    public static void output(String out){
        if(out.contains("error")) {
            totalErrorsEncountered.add(out);
        }
        System.out.println(out);
    }

}