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
  public static void main(String[] args) throws IOException {
    // Step 1: Read the Input
    BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
    String[] nmq = br.readLine().split(" ");
    int n = Integer.parseInt(nmq[0]);
    int m = Integer.parseInt(nmq[1]);
    int p = Integer.parseInt(nmq[2]);

    int[] sales = new int[n];
    ArrayList<Arc> arcs = new ArrayList<>();

    for (int i = 0; i < n; i++) {
      sales[i] = Integer.parseInt(br.readLine());
    }

    for (int i = 0; i < m; i++) {
      String[] uvw = br.readLine().split(" ");
      int u = Integer.parseInt(uvw[0]) - 1;
      int v = Integer.parseInt(uvw[1]) - 1;
      int w = Integer.parseInt(uvw[2]);
      arcs.add(new Arc(u, v, w));
    }

    br.close();

    // Step 2: Create the Flow Network
    int source = 2 * n;
    int sink = 2 * n + 1;
    ArrayList<Arc> newArcs = new ArrayList<>();

    for (int i = 0; i < n; i++) {
      newArcs.add(new Arc(source, i, sales[i] * p));
    }

    for (Arc arc : arcs) {
      newArcs.add(new Arc(arc.u, n + arc.v, arc.c));
      newArcs.add(new Arc(arc.v, n + arc.u, arc.c));
    }

    for (int i = 0; i < n; i++) {
      newArcs.add(new Arc(i, sink, Long.MAX_VALUE));
    }

    // FlowNetwork flowNetwork = new FlowNetwork(newArcs.size(), 2 * n + 2, source,
    // sink, newArcs);

    // // Step 3: Use the Dinic algorithm to find the max flow
    // FlowResults result = flowNetwork.dinic();

    // // Step 4: Run BFS on the residual graph to find all reachable nodes from 's'
    // ArrayList<Integer> reachable = flowNetwork.bfsResidualGraph(result.resCap,
    // source); // Modified this line

    // // Step 5: Output the result
    // BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(System.out));
    // long maxProfit = 0;
    // ArrayList<Integer> stations = new ArrayList<>();

    // for (Integer i : reachable) {
    // if (i != source && i != sink) {
    // maxProfit += sales[i];
    // stations.add(i + 1);
    // }
    // }

    // bw.write(maxProfit + " " + stations.size() + "\n");
    // for (int i = 0; i < stations.size(); i++) {
    // bw.write(stations.get(i) + (i == stations.size() - 1 ? "\n" : " "));
    // }

    // bw.close();
  }
}
