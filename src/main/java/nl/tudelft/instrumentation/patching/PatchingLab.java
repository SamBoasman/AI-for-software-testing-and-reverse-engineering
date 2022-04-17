package nl.tudelft.instrumentation.patching;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.utils.Log;
import nl.tudelft.instrumentation.symbolic.PathTracker;
import nl.tudelft.instrumentation.symbolic.SymbolicExecutionLab;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.sql.SQLOutput;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class PatchingLab {
        // Timer
        static long START_TIME = System.currentTimeMillis();
        static long END_TIME = START_TIME + (60 * 1000 * 5);

        static Random r = new Random();
        static boolean isFinished = false;

        static Map<String, Integer> operators = new HashMap<String, Integer>();

        // Keeps track of failures per operator
        static HashMap<Integer, Integer> OP_Failures = new HashMap<>();
        // Keeps track of success per operator
        static HashMap<Integer, Integer> OP_Success = new HashMap<>();
        // Keeps track of failed and passing count per generation
        static int count_failed = 0;
        static int count_passing = 0;
        static HashMap<Integer, Float> tarantula_score = new HashMap<>();
        static double best_fitness = Integer.MIN_VALUE;

        // Keeps track all encountered operators.
        static HashSet<String> total_operators =  new HashSet<>();
        // Keeps track of the encountered operators for current run.
        static HashMap<Integer, Integer> curr_operators = new HashMap<>();

        static String[] curr_individual;
        static List<String[]> population = new ArrayList<String[]>();
        final static int POPULATION_SIZE = 10;
        // list to keep the individuals and apply roulette selection, crossover, etc.
        static ArrayList<Population_individual> all_populations = new ArrayList<>();
        // complementary array.
        static ArrayList<Population_individual> best_individuals = new ArrayList<>();

        // create a hash map list to pick the best individuals only with highest probabilities.
        static HashMap<Integer, Float> sorted_probabilities = new HashMap<>();
        // best n-individuals to get to the next generation without picking.
        final static int BEST_INDIVIDUALS = 3;
        // Number of individuals that need to be mutated.
        final static int MUTATION_SIZE = 3;
        // Number of genes that need to be mutated.
        final static int GENE_MUTATION_SIZE = 2;

        //Bookkeeping
        static int NUM_GEN = 0;
        static String PROBLEM = "Problem12-2";
        static List<String[]> data = new ArrayList<>();

        static void initialize(){
                // initialize the population based on OperatorTracker.operators
                // This is completely up to you. You can pick a population of size X and you can create X number of
                // random individuals. This would be your initial population. An individual in this could is a list of
                // operators that should be used for the program. Do make sure that the individual does have as
                // many operators as the OperatorTracker.operators attribute. As an example, if there are only
                // 5 binary operators used in the problem file, then an individual would look something like this:
                // individual = [“==”, “<”, “!=”, “==”, “>=”] You can see the list of operators as the
                // gene of the individual.

                // Generate an initial population of size POPULATION_SIZE
                for (int i=1; i < POPULATION_SIZE; i++) {
                        String[] new_individual = OperatorTracker.operators.clone();
                        population.add(new_individual);
                }
        }

        /**
         *  encounteredOperator gets called for each operator encountered while running tests
         * @param operator
         * @param left
         * @param right
         * @param operator_nr
         * @return
         */
        static boolean encounteredOperator(String operator, int left, int right, int operator_nr){
                // Do something useful
                // Save that we encountered operator_nr for current_test.
                String id = OperatorTracker.current_test + "_" + operator_nr;

                // No need to add id to total_operators or count if operator has been encountered before.
                if(total_operators.contains(id)){
                        String replacement = OperatorTracker.operators[operator_nr];
                        if (replacement.equals("!=")) return left != right;
                        if (replacement.equals("==")) return left == right;
                        if (replacement.equals("<")) return left < right;
                        if (replacement.equals(">")) return left > right;
                        if (replacement.equals("<=")) return left <= right;
                        if (replacement.equals(">=")) return left >= right;
                        return false;
                }
                total_operators.add(id);

                // Compute how frequently an operator is used in a test
                Integer curr = curr_operators.get(operator_nr);
                if (curr != null) {
                        curr_operators.put(operator_nr, curr + 1);
                } else {
                        curr_operators.put(operator_nr, 1);
                }

                String replacement = OperatorTracker.operators[operator_nr];
                if (replacement.equals("!=")) return left != right;
                if (replacement.equals("==")) return left == right;
                if (replacement.equals("<")) return left < right;
                if (replacement.equals(">")) return left > right;
                if (replacement.equals("<=")) return left <= right;
                if (replacement.equals(">=")) return left >= right;
                return false;
        }

        static boolean encounteredOperator(String operator, boolean left, boolean right, int operator_nr){
                // Do something useful
                // Save that we encountered operator_nr for current_test.
                String id = OperatorTracker.current_test + "_" + operator_nr;

                // No need to add id to total_operators or count if operator has been encountered before.
                if(total_operators.contains(id)) {
                        String replacement = OperatorTracker.operators[operator_nr];
                        if(replacement.equals("!=")) return left != right;
                        if(replacement.equals("==")) return left == right;
                        return false;
                }
                total_operators.add(id);

                // Compute how frequently an operator is used in a test
                Integer curr = curr_operators.get(operator_nr);
                if (curr != null) {
                        curr_operators.put(operator_nr, curr + 1);
                } else {
                        curr_operators.put(operator_nr, 1);
                }

                String replacement = OperatorTracker.operators[operator_nr];
                if(replacement.equals("!=")) return left != right;
                if(replacement.equals("==")) return left == right;
                return false;
        }

        // Sorts hashmap by value.
        public static HashMap<Integer, Float> sort(HashMap<Integer, Float> map) {
                // Create a list from elements of HashMap
                List<Map.Entry<Integer, Float>> list =
                        new LinkedList<>(map.entrySet());

                // Sort the list
                Collections.sort(list, Collections.reverseOrder(Map.Entry.comparingByValue()));

                // Put data from sorted list to hashMap.
                HashMap<Integer, Float> sorted = new LinkedHashMap<>();
                for (Map.Entry<Integer, Float> i : list) {
                        sorted.put(i.getKey(), i.getValue());
                }
                return sorted;
        }

        public static void calcTarantulaHelper() {
                count_passing = 0;
                count_failed = 0;

                for (int i = 0; i < OperatorTracker.tests.size(); i++) {
                        boolean res = OperatorTracker.runTest(i);

                        // Save whether the test passed or not for calculating tarantula score.
                        if (res) {
                                count_passing += 1;
                                for (Map.Entry <Integer,Integer> entry : curr_operators.entrySet()){
                                        // Add operator to map if not in it, else +1 to operator in map.
                                        if (!OP_Success.containsKey(entry.getKey())) {
                                                OP_Success.put(entry.getKey(), entry.getValue());
                                        } else {
                                                OP_Success.put(entry.getKey(), OP_Success.get(entry.getKey()) + entry.getValue());
                                        }
                                }
                        } else {
                                // Compute how frequently an operator is used in a failing test for fault localization.
                                count_failed += 1;
                                for (Map.Entry <Integer,Integer> entry : curr_operators.entrySet()){
                                        if (!OP_Failures.containsKey(entry.getKey())) {
                                                OP_Failures.put(entry.getKey(), entry.getValue());
                                        } else {
                                                OP_Failures.put(entry.getKey(), OP_Failures.get(entry.getKey()) + entry.getValue());
                                        }
                                }
                        }
                        // Reset counts for new generation.
                        curr_operators.clear();
                        total_operators.clear();
                }

                // Uses number of failing tests as a fitness value
                // double fitness = (0.1 * count_passing) + (10 * count_failed);
                double fitness = (double) count_passing / OperatorTracker.tests.size();
                System.out.println("count_passing: " + count_passing + " count_failed: " + count_failed);

                calcTarantula();
                all_populations.add(new Population_individual(fitness, sort(tarantula_score), curr_individual));

                // Save fitness if better than curr best_fitness.
                if (fitness > best_fitness) {
                        best_fitness = fitness;
                } else {
                        System.out.println("best fitness not updated");
                }
                System.out.println("Best fitness: " + best_fitness);
        }

        public static void calcTarantula() {
                // From lecture slides
                for (int operation_nr = 0; operation_nr < OperatorTracker.operators.length; operation_nr++) {
                        int Passed = 0, Failed = 0;
                        float Tarantula = 0;
                        // if operation_nr is on the hashmaps, then add get the value and use it to calculate tarantula score.
                        if (OP_Success.containsKey(operation_nr)) Passed = OP_Success.get(operation_nr);
                        if (OP_Failures.containsKey(operation_nr)) Failed = OP_Failures.get(operation_nr);

                        float Failed_Metric = ((float) Failed) / count_failed;
                        float Passed_Metric = ((float) Passed) / count_passing;
                        Tarantula = Failed_Metric / (Failed_Metric + Passed_Metric);
                        // for the operators that doesn't have any tests covering them
                        // set Tarantula to 0.
                        if (Double.isNaN(Tarantula)) Tarantula = 0;
                        tarantula_score.put(operation_nr, Tarantula);
                }

        }

        /**
         * Creates normalized probabilities based as well as probabilities for roulette wheel selection
         * @return
         */
        public static void getProbabilities() {
                double[] probabilities = new double[all_populations.size()];
                int i = 0;
                // calculate sum of the fitness values.
                double sum_fit = all_populations.stream()
                        .map(item -> item.fitness_score)
                        .reduce(0.0, (a, b) -> a + b);

                for (Population_individual p : all_populations) {

                        double individual_score = p.fitness_score / sum_fit;
                        System.out.println("individual_score: " + p.fitness_score + " / " + sum_fit + " = " + individual_score);

                        sorted_probabilities.put(i, (float) p.fitness_score);
                        i++;
                }
        }

        /**
         * Creates new off spring using crossover and mutation with roulette selection.
         */
        static void reproduction(){
                getProbabilities();
                sorted_probabilities = sort(sorted_probabilities);
                Object[] keys = sorted_probabilities.keySet().toArray();

                // Sort population from best to worst fitness.
                for (Object key : keys){
                        Integer best_index = (Integer) key;
                        // Select individuals from population with the best fitness.
                        if (population.size() < BEST_INDIVIDUALS) {
                                // Save best individuals
                                best_individuals.add(all_populations.get(best_index));
                        }

                        population.add(all_populations.get(best_index).individual);

                        if (population.size() == POPULATION_SIZE) {
                                break;
                        }
                }

                // CROSSOVER
                crossover();

                // MUTATION for #BEST_INDIVIDUALS of the population
                for (int i = 0; i < BEST_INDIVIDUALS; i ++){
                        mutation(best_individuals.get(i).tarantula_score, i);
                }
        }

        /**
         * One-point crossover:
         *      Lists all possible cut points and randomly selects one cut point from the list
         */
        public static void crossover() {
                System.out.println("===========================================CROSSOVER=========================================");

                // Sorted on best fitness, so skip first #BEST_INDIVIDUALS.
                int i = 0;
                while( i < BEST_INDIVIDUALS){
                        String[] first = population.get(i);
                        String[] second = population.get(i + 1);
                        // Selects random point to crossover.
                        int crossover = r.nextInt(first.length);

                        // Swaps two operators
                        for (int j = crossover; j < first.length; j++) {

                                String tmp = first[j];
                                first[j] = second[j];
                                second[j] = tmp;
                        }
                        population.set(i, first);
                        population.set(i+1, second);

                        i+= 2;
                }
        }

        /**
         * 1) Randomly select one statement (node) to
         * mutate among the top k suspicious statement
         * 2) Mutate the selected statement
         * • Delete statement
         * • Add statement (if, method call, etc.)
         * • Replace variable
         * • Replace constant
         * • Replace method call
         *
         * @param tarantula
         * @param index
         */
        public static void mutation(HashMap<Integer, Float> tarantula, int index) {
                System.out.println("===========================================MUTATION=========================================");

                String [] indiv = Arrays.copyOf(population.get(index), population.get(index).length);
                int j = 0 ;
                float[] best_mutations = new float[OperatorTracker.operators.length];
                int[] best_indices = new int[OperatorTracker.operators.length];
                for (Map.Entry<Integer, Float> entry : tarantula.entrySet()){
                        // Only need a population size of OperatorTracker.operators.length
                        if (j>=OperatorTracker.operators.length) {
                                break;
                        }
                        best_mutations[j] = entry.getValue();
                        best_indices[j] = entry.getKey();
                        j++;
                }
                // Selects the change operations for mutation.
                ArrayList<Integer> operations_picked = roulette(best_mutations);
                System.out.println("Operations picked: " + operations_picked);

                // Mutatates operation based on operations_picked.
                for (int selected_index : operations_picked){
                        String temp = mutate(indiv[best_indices[selected_index]]);
                        indiv[best_indices[selected_index]] = temp;
                }
                // set the new curr_sample (after mutating) to old one.
                population.set(index, indiv);
        }

        // Possible operators
        static Map<Integer, String> operator_options = new HashMap<Integer, String>() {{
                put(0, "==");
                put(1, "!=");
                put(2, "<");
                put(3, ">");
                put(4, "<=");
                put(5, ">=");
        }};

        /**
         * Mutates an operator to a random other one.
         * @param curr
         * @return
         */
        static String mutate(String curr) {
                int ran = r.nextInt(6);
                while (operator_options.get(ran).equals(curr)) {
                        ran = r.nextInt(6);
                }
                return operator_options.get(ran);
        }

        /**
         * https://stackoverflow.com/questions/177271/roulette-selection-in-genetic-algorithms
         *
         * Calculates the occurrence probabilities for each operator.
         * Then create GENE_MUTATION_SIZE amount of changes using the probability.
         *
         * @param nums, an array containing the tarantula scores for the individual
         * @return changes, an array containing the change for each operator.
         */
        static ArrayList<Integer> roulette(float[] nums){
                float [] occur_prob = new float [nums.length];
                int j , i = 0;
                float sum_probabilities = 0;

                float sum_tarantula = 0;
                for ( j = 0; j < nums.length; j++){
                        sum_tarantula += nums[j];
                }

                for ( j = 0 ; j < nums.length; j ++){
                        float ind_sc = nums[j] / sum_tarantula;
                        occur_prob[j] = sum_probabilities + ind_sc;
                        sum_probabilities += ind_sc;
                }

                ArrayList<Integer> changes = new ArrayList<>();
                while (changes.size() < GENE_MUTATION_SIZE) {
                        double rand = r.nextDouble();
                        // Creates a change for each operator based on its occurence probability.
                        for (i = 0; i < occur_prob.length; i++){
                                if (rand <= occur_prob[i]){
                                        // If the operator is already used, don't use it again.
                                        if (!changes.contains(i)) {
                                                changes.add(i);
                                        }
                                        break;
                                }
                        }
                }
                return changes;
        }

        static void run() {
                initialize();

                // Place the code here you want to run once:
                // You want to change this of course, this is just an example
                // Tests are loaded from resources/tests.txt, make sure you put in the right tests for the right problem!
                System.out.println("Entered run");

                // Loop here, running your genetic algorithm until you think it is done
                while (System.currentTimeMillis() < END_TIME) {
                        // Do things!
                        // https://www.baeldung.com/java-genetic-algorithm

                        // If there are more populations to be run, try next population
                        curr_individual = population.remove(0);
                        OperatorTracker.operators = curr_individual.clone();

                        System.out.println(population.size());

                        System.out.println("===========================================CALCTARANTULAHELPER=========================================");
                        calcTarantulaHelper();

                        // If no more populations, then create new
                        if (population.isEmpty()){
                                System.out.println("===========================================REPRODUCE=========================================");
                                reproduction();

                                // Bookkeeping
                                data.add(new String[]{Integer.toString(NUM_GEN), Double.toString(best_fitness)});
                                NUM_GEN++;
                        }

                        System.out.println("Survival of the fittest size: " + sorted_probabilities.size());
                        // Clear tarantula scores, failures and success for next generation.
                        tarantula_score.clear();
                        OP_Failures.clear();
                        OP_Success.clear();
                }

                // Bookkeeping for csv file
                try {
                        writeToCSV();
                        writeToFile();
                } catch (IOException e) {
                        e.printStackTrace();
                }

        }

        static String convertToCSV(String[] data) {
                return Stream.of(data)
                        .map(PatchingLab::escapeSpecialCharacters)
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
                File csvOutputFile = new File("docs/lab3/" + PROBLEM + "/fitness_" + PROBLEM + ".csv");
                try (PrintWriter pw = new PrintWriter(csvOutputFile)) {
                        data.stream()
                                .map(PatchingLab::convertToCSV)
                                .forEach(pw::println);
                }
        }

        static void writeToFile() {
                try {
                        FileWriter myWriter = new FileWriter("docs/lab3/" + PROBLEM + "/output.txt", true);
                        myWriter.write(PROBLEM + "\n\n");

                        myWriter.write("best fitness: " + best_fitness + "\n");
                        myWriter.write("No. of generations run: " + NUM_GEN + "\n");
                        myWriter.close();
                        System.out.println("Successfully wrote to the file.");
                } catch (IOException e) {
                        System.out.println("An error occurred.");
                        e.printStackTrace();
                }

        }

        public static void output(String out){
                // This will get called when the problem code tries to print things,
                // the prints in the original code have been removed for your convenience

                // System.out.println(out);
        }

        private static class Population_individual {
                // keep track for each Sample in population, the fitness score,
                // and the tarantula score.
                private double fitness_score;
                private HashMap<Integer, Float> tarantula_score = new HashMap<>();
                private String[] individual;

                public Population_individual(double fitness_score, HashMap<Integer, Float> tarantula_score, String[] individual) {
                        this.fitness_score = fitness_score;
                        this.tarantula_score = tarantula_score;
                        this.individual = individual;
                }

                @Override
                public String toString() {
                        return "Population_individual: fitness_score=" + fitness_score +
                                ", tarantula_score=" + tarantula_score.toString();
                }
        }
}