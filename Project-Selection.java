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

  public static int N, M, n, m;

  // public static ArrayList<Integer> bfs(FlowResults fR) {

  // return null;
  // }

  public static ArrayList<Integer> bfs(FlowResults fR) {
    // Initialize the array to keep track of visited nodes
    boolean[] visited = new boolean[N];

    // Initialize the queue for BFS and add the starting node (0)
    Queue<Integer> queue = new LinkedList<>();
    queue.add(0);
    visited[0] = true;

    // Initialize the result ArrayList
    ArrayList<Integer> ans = new ArrayList<>();

    while (!queue.isEmpty()) {
      int current = queue.poll();

      // Check all adjacent edge indices of the current node
      for (int edgeIndex : fR.graph.get(current)) {
        int nextNode = fR.dest.get(edgeIndex);
        long edgeWeight = fR.resCap.get(edgeIndex);

        // Check if the edge has weight > 0 and nextNode is not visited
        if (edgeWeight > 0 && !visited[nextNode]) {
          queue.add(nextNode);
          visited[nextNode] = true;

          // Check if the index of the reachable node is between 1 and n
          if (nextNode >= 1 && nextNode <= n) {
            ans.add(nextNode);
          }
        }
      }
    }

    return ans;
  }

  public static void main(String[] args) throws IOException {
    final int inf = Integer.MAX_VALUE;

    // total profit without paying cleaning cost
    long w = 0L;

    // Step 1: Read Inputs and Build Arcs
    BufferedReader br = new BufferedReader(new InputStreamReader(System.in));

    String[] line1 = br.readLine().split(" ");
    assert line1.length == 3;
    n = Integer.parseInt(line1[0]); // n is the number of vertices
    m = Integer.parseInt(line1[1]); // m is the number of edges
    int p = Integer.parseInt(line1[2]); // p is the multiplier
    N = 2 + n + m;
    M = 3 * m + n;

    ArrayList<Arc> arcs = new ArrayList<>(); // arcs store all edges of the input graph G'

    for (int i = 1; i <= n; i++) {
      int s = Integer.parseInt(br.readLine()) * p;
      w += s;
      arcs.add(new Arc(0, i, s));
    }

    for (int i = 1; i <= m; i++) {
      String[] uvc = br.readLine().split(" ");
      // int u = Integer.parseInt(uvc[0]);
      // int v = Integer.parseInt(uvc[1]);
      // int c = Integer.parseInt(uvc[2]);
      arcs.add(new Arc(Integer.parseInt(uvc[0]), n + i, inf)); // edge from u to uv
      arcs.add(new Arc(Integer.parseInt(uvc[1]), n + i, inf)); // edge from v to uv
      arcs.add(new Arc(n + i, n + m + 1, Integer.parseInt(uvc[2]))); // edge from uv to t
    }

    br.close();

    // Step 2: Create the Flow Network
    final int source = 0;
    final int sink = m + n + 1;

    FlowNetwork fN = new FlowNetwork(arcs.size(), 2 + m + n, source, sink, arcs);

    // Step 3: Use the Dinic algorithm to find the max flow
    FlowResults fR = fN.dinic();

    // Step 4: Use bfs to get all reachable nodes from s
    ArrayList<Integer> output = bfs(fR);

    // Step 5: Output the result
    BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(System.out));

    bw.write(Integer.toString((int) (w - fR.maxFlow)));
    bw.write(" ");
    bw.write(Integer.toString(output.size()));
    // bw.newLine();
    bw.write("\n");

    for (int i = 0; i < output.size(); i++) {
      bw.write(Integer.toString(output.get(i)));
      if (i != output.size() - 1)
        bw.write(" ");
    }
    bw.write("\n");

    bw.close();
  }
}