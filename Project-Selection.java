import java.io.*;
import java.util.*;

// import java.util.ArrayDeque;
// import java.util.ArrayList;
// import java.util.StringTokenizer;

class FlowResults {
  ArrayList<ArrayList<Integer>> graph;
  Long maxFlow;
  ArrayList<Long> resCap;
  ArrayList<Integer> dest;

  public FlowResults() {
  }
}

class Arc {
  int u;
  int v;
  long c;

  public Arc(int u, int v, long c) {
    this.u = u;
    this.v = v;
    this.c = c;
  }
}

class NamedTuple {
  int curr;
  long bottleneck;
  int bottleneckStart;

  public NamedTuple(int curr, long bottleneck, int bottleneckStart) {
    this.curr = curr;
    this.bottleneck = bottleneck;
    this.bottleneckStart = bottleneckStart;
  }
}

class FlowNetwork {
  int m;
  int n;
  int s;
  int t;
  ArrayList<Long> cap;
  ArrayList<Integer> dest;
  ArrayList<ArrayList<Integer>> graph;

  public FlowNetwork(int m, int n, int s, int t, ArrayList<Arc> arcs) {
    this.m = m;
    this.n = n;
    this.s = s;
    this.t = t;

    cap = new ArrayList<Long>(2 * m);
    for (long i = 0; i < 2 * m; i++) {
      cap.add(0L);
    }

    dest = new ArrayList<Integer>(2 * m);

    graph = new ArrayList<>(n);
    for (long i = 0; i < n; i++) {
      graph.add(new ArrayList<>());
    }

    int edgeIdx = 0;
    for (Arc arc : arcs) {
      cap.set(edgeIdx, arc.c);
      graph.get(arc.u).add(edgeIdx++);
      graph.get(arc.v).add(edgeIdx++);
      dest.add(arc.v);
      dest.add(arc.u);
    }
  }

  private void computeDistances(ArrayList<Integer> distances, ArrayList<Integer> q, ArrayList<Long> resCap) {
    for (int i = 0; i < n; i++) {
      distances.set(i, -1);
    }
    distances.set(s, 0);

    int qs = 0;
    int qe = 1;
    q.set(0, s);

    while (qs < qe && distances.get(t) == -1) {
      int v = q.get(qs);
      qs++;
      if (distances.get(t) != -1 && distances.get(v) >= distances.get(t))
        break;

      for (int idx : graph.get(v)) {
        int w = dest.get(idx);
        if (resCap.get(idx) > 0 && distances.get(w) == -1) {
          distances.set(w, distances.get(v) + 1);
          q.set(qe, w);
          qe++;
        }
      }
    }
  }

  private long dinicAugment(ArrayList<Long> resCap, ArrayList<Integer> distances, ArrayList<Integer> ptrs) {
    long sSize = graph.get(s).size();
    long ans = 0;
    int curr = s;
    int bottleneckStart = -1;
    long bottleneck = Long.MAX_VALUE;

    ArrayDeque<NamedTuple> vertices = new ArrayDeque<>();

    if (ptrs.get(s) < sSize) {
      int idx = graph.get(s).get(ptrs.get(s));
      while (ptrs.get(s) < sSize && (distances.get(dest.get(idx)) != distances.get(s) + 1 || resCap.get(idx) == 0)) {
        ptrs.set(s, ptrs.get(s) + 1);
        if (ptrs.get(s) != graph.get(s).size())
          idx = graph.get(s).get(ptrs.get(s));
      }
    }

    while (ptrs.get(s) < sSize) {
      while (curr != t && ptrs.get(curr) < graph.get(curr).size()) {
        vertices.addFirst(new NamedTuple(curr, bottleneck, bottleneckStart));
        int idx = graph.get(curr).get(ptrs.get(curr));
        if (resCap.get(idx) < bottleneck) {
          bottleneck = resCap.get(idx);
          bottleneckStart = curr;
        }
        int next = dest.get(idx);

        if (ptrs.get(next) < graph.get(next).size()) {
          int idx2 = graph.get(next).get(ptrs.get(next));
          while (ptrs.get(next) < graph.get(next).size() &&
              (distances.get(dest.get(idx2)) != distances.get(next) + 1 || resCap.get(idx2) == 0)) {
            ptrs.set(next, ptrs.get(next) + 1);
            if (ptrs.get(next) != graph.get(next).size())
              idx2 = graph.get(next).get(ptrs.get(next));
          }
        }
        curr = next;
      }

      if (curr == t) {
        int curr2;
        while (!vertices.isEmpty()) {
          NamedTuple tup = vertices.removeFirst();
          curr2 = tup.curr;
          int idx = graph.get(curr2).get(ptrs.get(curr2));
          int revIdx = (cap.get(idx) == 0) ? idx - 1 : idx + 1;
          resCap.set(idx, resCap.get(idx) - bottleneck);
          resCap.set(revIdx, resCap.get(revIdx) + bottleneck);

          while (ptrs.get(curr2) < graph.get(curr2).size() &&
              (distances.get(dest.get(idx)) != distances.get(curr2) + 1 || resCap.get(idx) == 0)) {
            ptrs.set(curr2, ptrs.get(curr2) + 1);
            if (ptrs.get(curr2) != graph.get(curr2).size())
              idx = graph.get(curr2).get(ptrs.get(curr2));
          }
        }
        ans += bottleneck;

        bottleneck = Long.MAX_VALUE;
        bottleneckStart = -1;
        curr = s;
      } else {
        int pred = vertices.getFirst().curr;
        while (ptrs.get(curr) == graph.get(curr).size() && !vertices.isEmpty()) {
          NamedTuple tup = vertices.removeFirst();
          curr = tup.curr;
          bottleneck = tup.bottleneck;
          bottleneckStart = tup.bottleneckStart;
          ptrs.set(curr, ptrs.get(curr) + 1);

          if (ptrs.get(curr) < graph.get(curr).size()) {
            int idx = graph.get(curr).get(ptrs.get(curr));
            while (ptrs.get(curr) < graph.get(curr).size() &&
                (distances.get(dest.get(idx)) != distances.get(curr) + 1 || resCap.get(idx) == 0)) {
              ptrs.set(curr, ptrs.get(curr) + 1);
              if (ptrs.get(curr) != graph.get(curr).size())
                idx = graph.get(curr).get(ptrs.get(curr));
            }
          }
        }

        if (vertices.isEmpty()) {
          bottleneck = Long.MAX_VALUE;
          bottleneckStart = -1;
          curr = s;
        }
      }
    }
    return ans;
  }

  FlowResults dinic() {
    long ans = 0;
    ArrayList<Long> resCap = new ArrayList<>(cap);
    ArrayList<Integer> q = new ArrayList<>(2 * n);
    for (long i = 0; i < 2 * n; i++) {
      q.add(0);
    }

    ArrayList<Integer> distances = new ArrayList<>(n);
    for (long i = 0; i < n; i++) {
      distances.add(-1);
    }

    ArrayList<Integer> ptrs = new ArrayList<>(n);
    for (long i = 0; i < n; i++) {
      ptrs.add(0);
    }

    computeDistances(distances, q, resCap);

    while (distances.get(t) != -1) {
      ans += dinicAugment(resCap, distances, ptrs);
      computeDistances(distances, q, resCap);
      for (int i = 0; i < n; i++) {
        ptrs.set(i, 0);
      }
    }

    FlowResults fr = new FlowResults();
    fr.dest = dest;
    fr.maxFlow = ans;
    fr.graph = graph;
    fr.resCap = resCap;
    return fr;
  }
}

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

    bw.flush();
    bw.close();
  }
}
