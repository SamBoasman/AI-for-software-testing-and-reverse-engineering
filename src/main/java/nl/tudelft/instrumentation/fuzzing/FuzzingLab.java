package nl.tudelft.instrumentation.fuzzing;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * You should write your own solution using this class.
 */
public class FuzzingLab {
        // Switch between Random and fuzzer Strat
        static final boolean HILL_CLIMB = false;
        static final String PROBLEM = "Problem15";
        private static final float K = 1;
        private static final int NUM_PERMUTATIONS = 10;
        private static final int NUM_RUNS = 100;

        static Random r = new Random();
        static List<String> currentTrace;
        static int traceLength = 10;
        static boolean isFinished = false;
        static int runCounter = 0;

        static float sumDistances = 0;

        // Best Trace so far
        static List<String> bestTrace = new ArrayList<String>();
        static float smallestRatio = Float.MAX_VALUE;
        static HashSet<Integer> bestVisitedBranches = new HashSet<>();  // Branches of the best trace found
        static float bestDistance = Float.MAX_VALUE;

        // visitedBranches for each trace and new permutation;
        static HashSet<Integer> visitedBranches = new HashSet<>();      // VisitedBranches for ran trace and previous ran visited branches
        static HashSet<Integer> totalVisitedBranches = new HashSet<>(); // visitedBracnhes of best permutation of all cycles


        // Keep track of errors
        static HashSet<String> totalErrorsEncountered = new HashSet<>();


        // Per permutation cycle, keep track of best distance and branch-coverage
        static HashMap<List<String>, HashSet<Integer>> branchesPerTrace = new HashMap<>();
        static HashMap<List<String>, Float> distancePerTrace = new HashMap<List<String>, Float>();

        static HashMap<List<String>, HashSet<Integer>> bestBranchesPerTrace = new HashMap<>();
        static HashMap<List<String>, Float> bestDistancePerTrace = new HashMap<>();

        // Permutations for a cycle (NUM_PERMUTATIONS)
        static List<List<String>> currPermutations = new ArrayList<>();
        static int permutationCounter = 0;

        // Keep track of bestTrace and best ratio in cycles


        // Explore at start then permutations on best trace
        static boolean firstRun = true;
        static boolean betterTraceFound = false;


        
        // Bookkeeping CSV
        static List<String[]> data = new ArrayList<>();


        static void initialize(String[] inputSymbols){
                data.add(new String[]{"RUN", "BRANCHES", "ERRORS"});
                // Initialise a random trace from the input symbols of the problem.
                currentTrace = generateRandomTrace(inputSymbols);
                currPermutations = getRandomPermutations(inputSymbols);
//                if(permutationCounter < NUM_PERMUTATIONS){
//                        currentTrace = fuzz(inputSymbols);
//                        permutationCounter++;
//                        System.out.println("Current input trace: " + currentTrace);
//                } else {
//                        System.out.println("----distance per trace----");
//                        System.out.println(distancePerTrace.toString());
//                }
                for(int i = 0; i < inputSymbols.length; i++){
                        System.out.println(inputSymbols.length);
                        System.out.println(inputSymbols[i]);
                }
        }

        /**
         * Write your solution that specifies what should happen when a new branch has been found.
         */
        static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {
//                System.out.println("New branch at: " + line_nr + " with condition: " + condition);

                // Calculate BranchDistance
                float distance = computeDistance(condition);
                visitedBranches.add(line_nr);
                totalVisitedBranches.add(line_nr);
//
//                System.out.println("Calculated branch distance: " + distance);

                sumDistances += distance;
//                System.out.println("Summed distance: " + sumDistances);
//                System.out.println("Visited branches: " + visitedBranches.size());
        }

        /**
         * Check for BOOL, UNARY, BINARY operators
         * @param condition
         * @return
         */
        static float computeDistance(MyVar condition) {
                float d = Integer.MIN_VALUE;
                float left_distance = -1;
                float right_distance = -1;

                ArrayList<Integer> string_value_left = new ArrayList<>();
                ArrayList<Integer> string_value_right = new ArrayList<>();

                switch(condition.type) {
                        case BOOL:
                                d = condition.value ? 0 : 1;
//                                System.out.println("BOOL condition: " + condition.value + " distance: " + d);
                                break;
                        case UNARY:
                                left_distance = distanceHelper(condition.left, new ArrayList<>());
                                d = handleUnary(condition, left_distance);
//                                System.out.println("UNARY condition: !" + condition.value + ", d: " + d);
                                break;
                        case BINARY:
                                left_distance = distanceHelper(condition.left, string_value_left);
                                right_distance = distanceHelper(condition.right, string_value_right);
                                d = handleBinary(condition, left_distance, right_distance, string_value_left, string_value_right);
//                                System.out.println("BINARY predicate: " + condition + " d: " + d);
                                break;
                }
                return d;
        }

        static float handleUnary(MyVar condition, float left_distance) {
                float branch_distance;
                switch(condition.operator) {
                        case "!":
                                branch_distance = 1 - left_distance;
                                return normalize(branch_distance);
                        default:
                                System.err.println("handleUnary err:" + condition.operator);
                                break;
                }
                return Integer.MIN_VALUE;
        }

        static float handleBinary(MyVar condition, float left_distance, float right_distance, ArrayList<Integer> left_string, ArrayList<Integer> right_string) {
                float branch_distance;
                switch(condition.operator){
                        case "||":
                                branch_distance = Math.min(left_distance, right_distance);
                                return normalize(branch_distance);
                        case "&&":
                                branch_distance = left_distance + right_distance;
                                return normalize(branch_distance);
                        case "==":
                                if(condition.type == TypeEnum.STRING || !left_string.isEmpty() || !right_string.isEmpty()) {
//                                        System.out.println("BINARY condition, string values, left: " + left_string + " right: " + right_string);
                                        branch_distance = computeStringDistance(left_string, right_string);
                                } else {
                                        branch_distance = Math.abs(left_distance - right_distance);
                                }
                                return normalize(branch_distance);
                        case "!=":
                                if(condition.type == TypeEnum.STRING) {
                                        branch_distance = !left_string.equals(right_string) ? 0 : 1;
                                } else {
                                        branch_distance = (left_distance != right_distance) ? 0 : 1;
                                }
                                return normalize(branch_distance);
                        case "<":
                                branch_distance = (left_distance < right_distance) ? 0 : left_distance - right_distance + K;
                                return normalize(branch_distance);
                        case "<=":
                                branch_distance = (left_distance <= right_distance) ? 0 : left_distance - right_distance;
                                return normalize(branch_distance);
                        case ">":
                                branch_distance = (left_distance > right_distance) ? 0 : right_distance - left_distance + K;
                                return normalize(branch_distance);
                        case ">=":
                                branch_distance = (left_distance > right_distance) ? 0 : right_distance - left_distance;
                                return normalize(branch_distance);
                        default:
                                System.err.println("handleBinary err: " + condition.operator);
                                break;
                }
                return Integer.MIN_VALUE;
        }

        static float distanceHelper(MyVar predicate, ArrayList<Integer> string_val) {
                float d = 0;
//                System.out.println("distanceHelper for type: " + predicate.type);
                switch(predicate.type){
                        case BOOL:
                                // Todo: normalize
                                d = predicate.value ? 0 : 1;
//                                System.out.println("distanceHelper BOOL: " + predicate + " d: " + d);
                                break;
                        case INT:
                                // Todo: cast to float
                                d = predicate.int_value;
//                                System.out.println("distanceHelper INT: " + predicate + " d: " + d);
                                break;
                        case STRING:
                                String str = predicate.str_value;
                                for(int i = 0; i < str.length();i++){
                                        // Cast to int --> ASCII
                                        string_val.add((int) str.charAt(i));
                                }
                                d = Integer.MIN_VALUE;
                                break;
                        case UNARY:
                                if(predicate.operator.equals("!")) {
                                        d = computeDistance(predicate);
                                } else {
                                        // Not sure ???
                                        d = 0;
                                }
//                                System.out.println("distanceHelper UNARY: " + predicate + " d: " + d);
                                break;
                        case BINARY:
                                d = computeDistance(predicate);
//                                System.out.println("distanceHelper BINARY: " + predicate + " d: " + d);
                                break;
                        default:
                                System.err.println("Should not be reached: " + predicate.type.toString());
                                break;
                }
                return d;
        }

        static float computeStringDistance(ArrayList<Integer> left, ArrayList<Integer> right){
                int m = left.size();
                int n = right.size();
                int[][] table = new int[m+ 1][n + 1];
                for (int i = 0; i <= m; i++) {
                        for (int j = 0; j <= n; j++) {
                                if (i == 0) {
                                        table[i][j] = j;
                                }else if (j == 0) {
                                        table[i][j] = i;
                                }else if (left.get(i - 1).equals(right.get(j - 1))){
                                        table[i][j] = table[i-1][j-1];
                                }else{
                                        table[i][j] = Math.abs(left.get(i-1) - right.get(j-1))+
                                                Math.min(Math.min(table[i][j-1], table[i-1][j]), table[i-1][j-1]);
                                }
                        }
                }
                //System.out.println("computeStringDistance: " + table[m][n]);
                return table[m][n];
        }

        static float normalize(float i) {
                return i/(i+1);
        }

        static List<String> fuzz(String[] inputSymbols, List<String> bestTrace, boolean newTraceFound) {
                if (newTraceFound) { // Fuzzing with best trace
                        currPermutations = getPermutations(bestTrace, inputSymbols);
                        return bestTrace;
                } else { // Fuzzing random traces
                        List<String> newTrace = generateRandomTrace(inputSymbols);
                        currPermutations = getRandomPermutations(inputSymbols);
                        return newTrace;
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

        /**
         *
         * @param inputSymbols
         * @return random permutations based on the original trace. By shuffling, deleting and adding symbols.
         */
        static List<List<String>> getRandomPermutations(String[] inputSymbols) {
                List<List<String>> permutations = new ArrayList<List<String>>();
                for (int i = 0; i < NUM_PERMUTATIONS; i++) {
                        // First shuffle the original trace
                        permutations.add(generateRandomTrace(inputSymbols));
                }
                return permutations;
        }

        static List<List<String>> getPermutations(List<String> trace, String[] inputSymbols) {
                List<List<String>> permutations = new ArrayList<List<String>>();

                int size = (int) Math.ceil(NUM_PERMUTATIONS/4);
                int remainder = NUM_PERMUTATIONS - 3 * size;

                permutations.addAll(getSinglePermutations(trace, size, inputSymbols));
                permutations.addAll(getDoublePermutations(trace, size, inputSymbols));
                permutations.addAll(getAddPermutations(trace, size, inputSymbols));
                permutations.addAll(getShuffledPermutations(trace, remainder, inputSymbols));
                return permutations;
        }

        static List<List<String>> getShuffledPermutations(List<String> trace, int n, String[] inputSymbols) {
                List<List<String>> permutations = new ArrayList<List<String>>();

                for (int i = 0; i < n; i++) {
                        List<String> newTrace = new ArrayList<String>(trace);
                        Collections.shuffle(newTrace);
                        permutations.add(newTrace);
                }
                return permutations;
        }

        static List<List<String>> getAddPermutations(List<String> trace, int n, String[] inputSymbols) {
                List<List<String>> permutations = new ArrayList<List<String>>();

                for (int i = 0; i < n; i++) {
                        List<String> newTrace = new ArrayList<String>(trace);
                        Random rand = new Random();
                        int m = rand.nextInt(trace.size());
                        // Add a random element from the symbols.
                        String newElement = inputSymbols[rand.nextInt(inputSymbols.length)];
                        // System.out.println("newElement to add: " + newElement);
                        newTrace.add(m, newElement);
                        permutations.add(newTrace);
                }
                return permutations;
        }

        static List<List<String>> getDeletePermutations(List<String> trace, int n, String[] inputSymbols) {
                List<List<String>> permutations = new ArrayList<List<String>>();

                for (int i = 0; i < n; i++) {
                        List<String> newTrace = new ArrayList<String>(trace);
                        Random rand = new Random();
                        // Delete a random element from the trace.
                        int m = rand.nextInt(trace.size());
                        newTrace.remove(m);
                        permutations.add(newTrace);
                }
                return permutations;
        }

        static List<List<String>> getSinglePermutations(List<String> trace, int n, String[] inputSymbols) {
                List<List<String>> permutations = new ArrayList<List<String>>();

                for (int i = 0; i < n; i++) {
                        List<String> newTrace = new ArrayList<String>(trace);

                        Random rand = new Random();
                        // Index of element to be changed.
                        int m = rand.nextInt(newTrace.size());
//                        System.out.println("m: " + m);
                        // Add a random element from the symbols.
                        String newElement = inputSymbols[rand.nextInt(inputSymbols.length)];
                        // System.out.println("newElement to add: " + newElement);
                        newTrace.set(m, newElement);

                        permutations.add(newTrace);
                }

                return permutations;
        }

        static List<List<String>> getDoublePermutations(List<String> trace, int n, String[] inputSymbols) {
                List<List<String>> permutations = new ArrayList<List<String>>();

                for (int i = 0; i < n; i++) {
                        List<String> newTrace = new ArrayList<String>(trace);

                        Random rand = new Random();
                        // Index of element to be changed.
                        int x = rand.nextInt(newTrace.size());
                        int y = rand.nextInt(newTrace.size());
                        while(x == y){
                                y = rand.nextInt(newTrace.size());
                        }
                        // Add a random element from the symbols.
                        String newXElement = inputSymbols[rand.nextInt(inputSymbols.length)];
                        String newYElement = inputSymbols[rand.nextInt(inputSymbols.length)];

                        newTrace.set(x, newXElement);
                        newTrace.set(y, newYElement);

                        permutations.add(newTrace);
                }

                return permutations;
        }

        static void run() {
                initialize(DistanceTracker.inputSymbols);

                while(!isFinished) {
                        DistanceTracker.runNextFuzzedSequence(currentTrace.toArray(new String[0]));

                        if(permutationCounter < NUM_PERMUTATIONS) { // Run permutation cycle
                                // Check for best trace
                                float ratioDistanceBranches = sumDistances / (sumDistances + visitedBranches.size());

                                if (ratioDistanceBranches < smallestRatio) {
                                        smallestRatio = ratioDistanceBranches;

                                        // Keep best trace
                                        bestTrace = currentTrace;
                                        bestVisitedBranches = visitedBranches;
                                        bestDistance = sumDistances;
                                        betterTraceFound = true;
                                }
                                // Reset for new permutation
                                sumDistances = 0;
                                visitedBranches = new HashSet<>();

                                // Setup next permutation
                                currentTrace = currPermutations.get(permutationCounter);
                                permutationCounter++;
                        } else {
                                System.out.println("========================================LOG " + runCounter + "========================================");
                                System.out.println("Total visited branches: " + totalVisitedBranches.size());
                                System.out.println("Total errors found: " + totalErrorsEncountered.size());
                                // Minimum distance

                                System.out.println("Best trace found: " + bestTrace);
                                System.out.println("Best trace branch distance: " + bestDistance);
                                System.out.println("Best trace visited branches: " + bestVisitedBranches.size());

                                System.out.println("========================================LOG " + runCounter + "========================================");

                                // Next Run
                                runCounter++;

                                // Reset for new Permutation cycle
                                branchesPerTrace = new HashMap<>();
                                distancePerTrace = new HashMap<>();
                                visitedBranches = new HashSet<>();
                                permutationCounter = 0;
                                smallestRatio = Float.MAX_VALUE;
                                sumDistances = 0;

                                // Get new sequence
                                if (HILL_CLIMB) {
                                        currentTrace = fuzz(DistanceTracker.inputSymbols, bestTrace, betterTraceFound);
                                } else {
                                        currentTrace = fuzz(DistanceTracker.inputSymbols, bestTrace, false);
                                }

                                data.add(new String[]{Integer.toString(runCounter), Integer.toString(totalVisitedBranches.size()), Integer.toString(totalErrorsEncountered.size())});
                                betterTraceFound = false;
                        }

                        if(!(runCounter < NUM_RUNS)) {
                              isFinished = true;
                        }
                }
                try {
                        writeToCSV();
                        writeToFile();
                } catch (IOException e) {
                        e.printStackTrace();
                }
        }

         static String convertToCSV(String[] data) {
                return Stream.of(data)
                        .map(FuzzingLab::escapeSpecialCharacters)
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
                                .map(FuzzingLab::convertToCSV)
                                .forEach(pw::println);
                }
        }

        static void writeToFile() {
                try {
                        FileWriter myWriter = new FileWriter("docs/lab1/" + PROBLEM + "/problem_errors.txt", true);
                        myWriter.write(PROBLEM + " (" + NUM_PERMUTATIONS + ", " + NUM_RUNS + ")\n\n");
                        myWriter.write("Best Trace: " + bestTrace + "\n");
                        myWriter.write("Best visited branches: " + bestVisitedBranches.size() + "\n");
                        myWriter.write("Best distance: " + bestDistance + "\n\n");

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

        /**
         * Method that is used for catching the output from standard out.
         * You should write your own logic here.
         * @param out the string that has been outputted in the standard out.
         */
        public static void output(String out){
                if(out.contains("error")) {
                        totalErrorsEncountered.add(out);
                }
                System.out.println(out);
        }
}