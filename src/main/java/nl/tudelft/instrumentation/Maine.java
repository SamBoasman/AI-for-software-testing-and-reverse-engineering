package nl.tudelft.instrumentation;

import java.io.FileNotFoundException;

public class Maine {
  public static void main(String[] args) throws FileNotFoundException {
    String filepath =
        System.getProperty("user.dir") + "/src/main/java/nl/tudelft/instrumentation/Main.java";
    args = new String[] {"-f", filepath, "-t", "branch"};
    Main.main(args);
  }
}
