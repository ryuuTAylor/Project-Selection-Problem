import java.io.*;
import java.util.*;

class Main {
  // Global bw
  static BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(System.out));

  // n is time, m is interval, k is maximum allowed bus number
  public static int n, m, k;

  // input C[i] for i = 1 to n
  public static int[] C;

  // OPT[i][j] for i = 1 to n+m-1, j = 1 to k
  public static long[][] OPT;

  // M[i][j] for i = 1 to n+m-1, j = 1 to k
  public static int[][] M;

  // flag
  public static int flag = 0;

  // Regular DP using our recurrance formula
  public static void dp() throws IOException {
    for (int i = 1; i <= n; i++) {
      for (int j = 1; j <= k; j++) {
        if (i == 1) {
          OPT[i][j] = (long) 0;
          M[i][j] = -1;
        } else if (j == 1) {
          for (int l = 1; l <= i - 1; l++)
            OPT[i][j] += (long) C[l] * (i - l);
          M[i][j] = -1;
        } else {
          if (i <= m) {
            OPT[i][j] = OPT[i][1];
            M[i][j] = -1;
          } else {
            long temp = 0;
            for (int l = i - m + 1; l <= i - 1; l++)
              temp += (long) C[l] * (i - l);
            OPT[i][j] = temp + OPT[i - m][j - 1];
            M[i][j] = i - m;
            for (int iprime = i - m - 1; iprime >= 1; iprime--) {
              temp += (long) C[iprime + 1] * (i - (iprime + 1)); // beware of OBO bugs
              if (OPT[iprime][j - 1] + temp < OPT[i][j]) { // can set to <=
                OPT[i][j] = OPT[iprime][j - 1] + temp;
                M[i][j] = iprime;
              }
            }
          }
          // Special treatment for the last bus
          if (i == n) {
            for (int iprime = n - 1; iprime >= Math.max(1, n - m + 1); iprime--) {
              int temp = 0;
              for (int x = iprime + 1; x <= n; x++) {
                temp += (long) C[x] * (iprime + m - x);
              }
              if (OPT[iprime][j - 1] + temp < OPT[n][j]) {
                flag = 1;
                OPT[n][j] = OPT[iprime][j - 1] + temp;
                M[n][j] = iprime;
              }
            }
          }
        }
      }
    }
    bw.write(Long.toString(OPT[n][k]));
    bw.newLine();
  }

  public static void backTrack() throws IOException {
    List<Integer> A = new ArrayList<>();
    if (flag == 1)
      A.add(M[n][k] + m);
    else
      A.add(n);
    int i = n, j = k;
    while (i > 0 && j > 0 && M[i][j] >= 1) {
      A.add(M[i][j]);
      i = M[i][j];
      j--;
    }
    for (int idx = A.size() - 1; idx >= 0; idx--) {
      bw.write(String.valueOf(A.get(idx)));
      if (idx > 0) {
        bw.write(" ");
      }
    }
    bw.newLine();
  }

  public static void main(String[] args) throws IOException {

    // // Record the start time
    // long startTime = System.nanoTime();

    BufferedReader br = new BufferedReader(new InputStreamReader(System.in));

    String[] line1 = br.readLine().split(" ");
    assert line1.length == 3;
    n = Integer.parseInt(line1[0]);
    m = Integer.parseInt(line1[1]);
    k = Integer.parseInt(line1[2]);

    C = new int[n + 1];
    OPT = new long[n + 1][k + 1];
    M = new int[n + 1][k + 1];

    String[] line2 = br.readLine().split(" ");
    assert line2.length == n;
    for (int i = 1; i <= n; i++) {
      C[i] = Integer.parseInt(line2[i - 1]);
    }

    br.close();

    dp();
    backTrack();

    // // Debugging
    // for (int i = 1; i <= n; i++) {
    // for (int j = 1; j <= k; j++) {
    // bw.write("OPT[" + i + "][" + j + "]: " + OPT[i][j]);
    // bw.newLine();
    // }
    // }

    // bw.write("You've run your java code!\n");

    // // Record the end time
    // long endTime = System.nanoTime();

    // // Calculate the runtime in milliseconds
    // long runtimeMilliseconds = (endTime - startTime) / 1000000;

    // bw.write("Runtime: " + Long.toString(runtimeMilliseconds) + " ms");

    bw.flush();
    bw.close();
  }
}
