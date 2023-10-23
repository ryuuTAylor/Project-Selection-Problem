#ifndef ALGO_CPP_FLOWNETWORK_H
#define ALGO_CPP_FLOWNETWORK_H

#include <cstdint>
#include <limits>
#include <vector>
#include <unordered_set>
#include <utility>
#include <queue>
#include <stack>
#include <iostream>
#include <limits.h>
#include <stdio.h>

namespace flow_network
{
  class Arc
  {
  public:
    uint64_t u;
    uint64_t v;
    uint64_t c;

    Arc(uint64_t u, uint64_t v, uint64_t c);
    Arc();
  };

  class FlowResults
  {
  public:
    FlowResults(std::vector<std::vector<uint64_t>> graph, std::vector<uint64_t> dest);
    uint64_t max_flow;
    std::vector<uint64_t> res_cap;
    const std::vector<std::vector<uint64_t>> graph;
    const std::vector<uint64_t> dest;
  };

  class FlowNetwork
  {

  public:
    FlowNetwork(uint64_t m, uint64_t n, uint64_t s, uint64_t t, const std::vector<Arc> &arcs);
    FlowResults dinic();

  private:
    std::vector<std::vector<uint64_t>> graph;
    uint64_t s;
    uint64_t t;
    uint64_t m;
    uint64_t n;
    std::vector<uint64_t> cap;
    std::vector<uint64_t> dest;
  };

}

#endif // ALGO_CPP_FLOWNETWORK_H

flow_network::Arc::Arc(uint64_t u, uint64_t v, uint64_t c) : u(u), v(v), c(c){};

flow_network::Arc::Arc() = default;

flow_network::FlowResults::FlowResults(std::vector<std::vector<uint64_t>> graph, std::vector<uint64_t> dest) : graph(
                                                                                                                   std::move(graph)),
                                                                                                               dest(std::move(dest)) {}

flow_network::FlowNetwork::FlowNetwork(uint64_t m, uint64_t n, uint64_t s, uint64_t t, const std::vector<Arc> &arcs)
    : m(m), n(n), s(s), t(t)
{
  cap = std::vector<uint64_t>(2 * m, 0);
  graph = std::vector<std::vector<uint64_t>>(n);
  uint64_t edge_idx = 0;
  for (auto &arc : arcs)
  {
    cap[edge_idx] = arc.c;
    graph[arc.u].push_back(edge_idx++);
    graph[arc.v].push_back(edge_idx++);
    dest.push_back(arc.v);
    dest.push_back(arc.u);
  }
}

#include <vector>
void compute_distances_faster(std::vector<uint64_t> &distances, std::vector<uint64_t> &q, const std::vector<uint64_t> &rescap,
                              const std::vector<std::vector<uint64_t>> &graph, const std::vector<uint64_t> &dest, uint64_t s,
                              uint64_t t)
{
  std::fill(distances.begin(), distances.end(), -1);
  uint64_t n = graph.size();

  distances[s] = 0;
  uint64_t qs = 0;
  uint64_t qe = 1;
  q[0] = s;

  while (qs < qe && distances[t] == -1)
  {
    uint64_t v = q[qs];
    qs++;
    if (distances[t] != -1 && distances[v] >= distances[t])
      break;
    for (uint64_t idx : graph[v])
    {
      uint64_t w = dest[idx];
      if (rescap[idx] > 0 && distances[w] == uint64_t(-1))
      {
        distances[w] = distances[v] + 1;
        q[qe] = w;
        qe++;
      }
    }
  }
}

// use some tricks to augment by a blocking flow in O(mn) time
uint64_t dinic_augment(std::vector<uint64_t> &rescap, const std::vector<uint64_t> &cap, std::vector<uint64_t> &ptrs,
                       const std::vector<uint64_t> &distances, const std::vector<std::vector<uint64_t>> &graph,
                       const std::vector<uint64_t> &dest, uint64_t s, uint64_t t)
{

  const uint64_t s_size = graph[s].size();

  uint64_t ans = 0;
  // each record [u, bottleneck_cap, bottleneck_start] means that there's a path from s to u with bottleneck edge leaving bottleneck_start of capacity bottleneck_cap
  std::stack<std::tuple<uint64_t, uint64_t, uint64_t>> vertices;

  // state of search
  uint64_t curr;
  uint64_t bottleneck;
  uint64_t bottleneck_start;

  // fix ptr for s, init first search
  {
    uint64_t idx = graph[s][ptrs[s]];
    while (ptrs[s] < graph[s].size() && (distances[dest[idx]] != distances[s] + 1 || rescap[idx] == 0))
    {
      ptrs[s]++;
      idx = graph[s][ptrs[s]];
    }

    bottleneck = std::numeric_limits<uint64_t>::max();
    bottleneck_start = -1;
    curr = s;
  }

  // while there's an edge leaving s in level graph
  while (ptrs[s] < s_size)
  {
    // basic invariant that I spammed everywhere

    // stop whenever we find t or a dead end (and don't put them on the stack, instead store using 3 state vars)
    while (curr != t && ptrs[curr] < graph[curr].size())
    {
      vertices.emplace(curr, bottleneck, bottleneck_start);

      uint64_t idx = graph[curr][ptrs[curr]];

      if (rescap[idx] < bottleneck)
      {
        bottleneck = rescap[idx];
        bottleneck_start = curr;
      }
      uint64_t next = dest[idx];

      // fix ptr for next (to check if it's a dead end)
      {
        uint64_t idx = graph[next][ptrs[next]];
        while (ptrs[next] < graph[next].size() &&
               (distances[dest[idx]] != distances[next] + 1 || rescap[idx] == 0))
        {
          ptrs[next]++;
          idx = graph[next][ptrs[next]];
        }
      }

      curr = next;

      {
        auto tup = vertices.top();
        uint64_t curr2 = std::get<0>(tup);
        uint64_t idx = graph[curr2][ptrs[curr2]];
        uint64_t revIdx = (cap[idx] == 0) ? idx - 1 : idx + 1;
      }
    }

    if (curr == t)
    {
      //            fprintf(stderr, "augmenting\n");
      uint64_t curr2;
      while (!vertices.empty())
      {
        auto tup = vertices.top();
        curr2 = std::get<0>(tup);

        // graph formation invariant: forward edges precede their neighboring backward edges
        uint64_t idx = graph[curr2][ptrs[curr2]];
        uint64_t revIdx = (cap[idx] == 0) ? idx - 1 : idx + 1;

        rescap[idx] -= bottleneck;
        rescap[revIdx] += bottleneck;

        while (ptrs[curr2] < graph[curr2].size() &&
               (distances[dest[idx]] != distances[curr2] + 1 || rescap[idx] == 0))
        {
          ptrs[curr2]++;
          idx = graph[curr2][ptrs[curr2]];
        }
        vertices.pop();
      }
      ans += bottleneck;

      // do another search
      bottleneck = std::numeric_limits<uint64_t>::max();
      bottleneck_start = -1;
      curr = s;
    }
    else
    {
      // delete edges leading to dead-end vertices

      uint64_t pred = std::get<0>(vertices.top()); // direct predecessor of node with outdegree 0

      while (ptrs[curr] == graph[curr].size() && !vertices.empty())
      { // curr has out-degree 0 in level graph

        auto tup = vertices.top();
        curr = std::get<0>(tup);
        bottleneck = std::get<1>(tup);
        bottleneck_start = std::get<2>(tup);

        vertices.pop();

        ptrs[curr]++; // discard the edge that led to the dead end

        { // discard other edges
          uint64_t idx = graph[curr][ptrs[curr]];
          while (ptrs[curr] < graph[curr].size() &&
                 (distances[dest[idx]] != distances[curr] + 1 || rescap[idx] == 0))
          {
            ptrs[curr]++;
            idx = graph[curr][ptrs[curr]];
          }
        }
      }

      // check that some pointer went up but not uselessly

      if (!vertices.empty())
      {
        bottleneck = bottleneck;
        bottleneck_start = bottleneck_start;
        curr = curr;
      }
      else
      {
        bottleneck = std::numeric_limits<uint64_t>::max();
        bottleneck_start = -1;
        curr = s;
      }
    }
  }

  return ans;
}

flow_network::FlowResults flow_network::FlowNetwork::dinic()
{
  uint64_t ans = 0;
  std::vector<uint64_t> rescap(cap);
  std::vector<uint64_t> q(2 * n);

  // result of BFS (to avoid actually manifesting the edges of the level graph)
  std::vector<uint64_t> distances(n, -1);
  std::vector<uint64_t> ptrs(n, 0); // ptr[u] == k  <==>  the first k neighbors of u are not in the level graph
                                    //    compute_distances(distances, rescap, graph, dest, s, t);
  compute_distances_faster(distances, q, rescap, graph, dest, s, t);

  while (distances[t] != uint64_t(-1))
  {
    //        fprintf(stderr, "t dist: %lld\n", distances[t]);
    ans += dinic_augment(rescap, cap, ptrs, distances, graph, dest, s, t);
    compute_distances_faster(distances, q, rescap, graph, dest, s, t);

    std::fill(ptrs.begin(), ptrs.end(), 0); // reset ptrs
  }

  FlowResults fr(graph, dest);
  fr.res_cap = rescap;
  fr.max_flow = ans;

  return fr;
}

using namespace std;

static int N, M, n, m;

vector<int> bfs(flow_network::FlowResults fR)
{
  // Initialize the array to keep track of visited nodes
  vector<bool> visited(N, false);

  // Initialize the queue for BFS and add the starting node (0)
  queue<int> queue;
  queue.push(0);
  visited[0] = true;

  // Initialize the result vector
  vector<int> ans;

  while (!queue.empty())
  {
    int current = queue.front();
    queue.pop();

    // Check all adjacent edge indices of the current node
    for (int edgeIndex : fR.graph[current])
    {
      int nextNode = fR.dest[edgeIndex];
      long edgeWeight = fR.res_cap[edgeIndex];

      // Check if the edge has weight > 0 and nextNode is not visited
      if (edgeWeight > 0 && !visited[nextNode])
      {
        queue.push(nextNode);
        visited[nextNode] = true;

        // Check if the index of the reachable node is between 1 and n
        if (nextNode >= 1 && nextNode <= n)
        {
          ans.push_back(nextNode);
        }
      }
    }
  }

  return ans;
}

int main()
{
  const int inf = INT_MAX;

  // total profit without paying cleaning cost
  long w = 0L;

  // Step 1: Read Inputs and Build Arcs
  int p;
  scanf("%d %d %d", &n, &m, &p); // n is the number of vertices, m is the number of edges, p is the multiplier
  N = 2 + n + m;
  M = 3 * m + n;

  vector<flow_network::Arc> arcs; // arcs store all edges of the input graph G'

  for (int i = 1; i <= n; i++)
  {
    int s;
    scanf("%d", &s);
    s *= p;
    w += s;
    arcs.push_back(flow_network::Arc(0, i, s));
  }

  for (int i = 1; i <= m; i++)
  {
    int u, v, c;
    scanf("%d %d %d", &u, &v, &c);
    arcs.push_back(flow_network::Arc(u, n + i, inf));       // edge from u to uv
    arcs.push_back(flow_network::Arc(v, n + i, inf));       // edge from v to uv
    arcs.push_back(flow_network::Arc(n + i, n + m + 1, c)); // edge from uv to t
  }

  // Step 2: Create the Flow Network
  const int source = 0;
  const int sink = m + n + 1;

  flow_network::FlowNetwork fN(arcs.size(), 2 + m + n, source, sink, arcs);

  // Step 3: Use the Dinic algorithm to find the max flow
  flow_network::FlowResults fR = fN.dinic();

  // Step 4: Use bfs to get all reachable nodes from s
  vector<int> output = bfs(fR);

  // Step 5: Output the result
  printf("%d %lu\n", (int)(w - fR.max_flow), output.size());

  for (size_t i = 0; i < output.size(); ++i)
  {
    printf("%d", output[i]);
    if (i != output.size() - 1)
      printf(" ");
  }

  printf("\n");

  return 0;
}
