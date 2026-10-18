#include <algorithm>
#include <cmath>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

struct Edge {
  int a;
  int b;
  long double p;
};

int n;
int m;
int entrance;
long double day_cost;
std::vector<long double> value;
std::vector<Edge> model_edges;
std::vector<std::vector<std::pair<int, int>>> g;
std::vector<int> comp;
std::vector<long double> profit;
std::vector<long double> fail_log;
std::vector<long double> conn;
std::vector<long double> dp;
std::vector<int> boundary;
std::vector<int> policy;

void ReadMap() {
  std::cin >> n >> m;
  std::cin >> day_cost >> entrance;
  --entrance;
  value.resize(n);
  for (int v = 0; v < n; ++v) {
    std::cin >> value[v];
  }
  model_edges.resize(m);
  g.resize(n);
  for (int e = 0; e < m; ++e) {
    std::cin >> model_edges[e].a >> model_edges[e].b >> model_edges[e].p;
    --model_edges[e].a;
    --model_edges[e].b;
    g[model_edges[e].a].emplace_back(model_edges[e].b, e);
    g[model_edges[e].b].emplace_back(model_edges[e].a, e);
  }
}

int Find(std::vector<int>& parent, int v) {
  if (parent[v] == v) {
    return v;
  }
  return parent[v] = Find(parent, parent[v]);
}

void Join(std::vector<int>& parent, std::vector<int>& rank, int u, int v) {
  u = Find(parent, u);
  v = Find(parent, v);
  if (u == v) {
    return;
  }
  if (rank[v] > rank[u]) {
    std::swap(u, v);
  }
  parent[v] = u;
  if (rank[u] == rank[v]) {
    ++rank[u];
  }
}

void Contract() {
  std::vector<int> parent(n);
  std::vector<int> rank(n, 1);
  for (int v = 0; v < n; ++v) {
    parent[v] = v;
  }
  for (auto edge : model_edges) {
    if (edge.p == 1) {
      Join(parent, rank, edge.a, edge.b);
    }
  }
  std::vector<int> index(n, -1);
  std::vector<long double> new_value;
  comp.resize(n);
  for (int v = 0; v < n; ++v) {
    int root = Find(parent, v);
    if (index[root] == -1) {
      index[root] = static_cast<int>(new_value.size());
      new_value.push_back(0);
    }
    comp[v] = index[root];
    new_value[comp[v]] += value[v];
  }
  std::vector<Edge> new_edges;
  for (auto edge : model_edges) {
    int a = comp[edge.a];
    int b = comp[edge.b];
    if (a != b) {
      new_edges.push_back({a, b, edge.p});
    }
  }
  entrance = comp[entrance];
  value = new_value;
  model_edges = new_edges;
  n = static_cast<int>(value.size());
}

int FirstVertex(int mask) {
  int v = 0;
  while (((mask >> v) & 1) == 0) {
    ++v;
  }
  return v;
}

void BuildMasks() {
  int size = 1 << n;
  std::vector<int> neighbors(n, 0);
  std::vector<std::vector<long double>> pair_log(n, std::vector<long double>(n));
  for (auto edge : model_edges) {
    neighbors[edge.a] |= (1 << edge.b);
    neighbors[edge.b] |= (1 << edge.a);
    pair_log[edge.a][edge.b] += std::log1p(-edge.p);
    pair_log[edge.b][edge.a] += std::log1p(-edge.p);
  }
  profit.assign(size, 0);
  boundary.assign(size, 0);
  fail_log.assign(size, 0);
  for (int mask = 1; mask < size; ++mask) {
    int v = FirstVertex(mask);
    int prev = mask & (mask - 1);
    profit[mask] = profit[prev] + value[v];
    boundary[mask] = (boundary[prev] | neighbors[v]) & ~mask;
    fail_log[mask] = fail_log[prev];
    for (int u = 0; u < n; ++u) {
      if (prev & (1 << u)) {
        fail_log[mask] += pair_log[v][u];
      }
    }
  }
}

long double FailCut(int a, int b) {
  return std::exp(fail_log[a | b] - fail_log[a] - fail_log[b]);
}

void BuildConn() {
  int size = 1 << n;
  std::vector<int> possible_neighbors(n, 0);
  for (auto edge : model_edges) {
    if (edge.p > 0) {
      possible_neighbors[edge.a] |= (1 << edge.b);
      possible_neighbors[edge.b] |= (1 << edge.a);
    }
  }
  conn.assign(size, 0);
  for (int mask = 1; mask < size; ++mask) {
    int root = mask & -mask;
    int reached = root;
    int pending = root;
    while (pending) {
      int v = FirstVertex(pending);
      pending &= (pending - 1);
      int next = possible_neighbors[v] & mask & ~reached;
      reached |= next;
      pending |= next;
    }
    if (reached != mask) {
      continue;
    }
    long double disconnected = 0;
    for (int sub = (mask - 1) & mask; sub; sub = (sub - 1) & mask) {
      if ((sub & root) && conn[sub] != 0) {
        disconnected += conn[sub] * FailCut(sub, mask ^ sub);
      }
    }
    conn[mask] = 1 - disconnected;
  }
}

void BuildDp() {
  int size = 1 << n;
  int full = size - 1;
  dp.assign(size, 0);
  policy.assign(size, -1);
  std::vector<long double> q(n);
  for (int mask = full; mask > 0; --mask) {
    if (!(mask & (1 << entrance)) || boundary[mask] == 0) {
      continue;
    }
    std::fill(q.begin(), q.end(), -day_cost);
    int remaining = full ^ mask;
    for (int sub = remaining; sub; sub = (sub - 1) & remaining) {
      int actions = sub & boundary[mask];
      if (conn[sub] == 0 || actions == 0) {
        continue;
      }
      long double probability = conn[sub] * FailCut(sub, remaining ^ sub);
      long double gain = probability * (profit[sub] + dp[mask | sub]);
      for (int v = 0; v < n; ++v) {
        if (actions & (1 << v)) {
          q[v] += gain;
        }
      }
    }
    for (int v = 0; v < n; ++v) {
      if ((boundary[mask] & (1 << v)) && q[v] > dp[mask]) {
        dp[mask] = q[v];
        policy[mask] = v;
      }
    }
  }
}

void Look(int v, std::vector<int>& state) {
  std::cout << "LOOK" << std::endl;
  for (std::size_t i = 0; i < g[v].size(); ++i) {
    std::string type;
    int id;
    int to;
    std::string status;
    std::cin >> type >> id >> to >> status;
    --id;
    --to;
    state[id] = status == "OK" ? 1 : 0;
  }
}

void Move(int e) {
  std::cout << "MOVE " << e + 1 << std::endl;
  std::string answer;
  std::cin >> answer;
}

int Dfs(int v, std::vector<int>& state, std::vector<bool>& used) {
  used[v] = true;
  int mask = 1 << comp[v];
  Look(v, state);
  for (auto [u, e] : g[v]) {
    if (!used[u] && state[e] == 1) {
      Move(e);
      mask |= Dfs(u, state, used);
      Move(e);
    }
  }
  return mask;
}

void Explore(int start) {
  std::vector<int> state(m, -1);
  while (true) {
    std::vector<bool> used(g.size(), false);
    int mask = Dfs(start, state, used);
    int v = policy[mask];
    if (v == -1) {
      std::cout << "END" << std::endl;
      std::string result;
      long double collected;
      int days;
      long double net;
      std::cin >> result >> collected >> days >> net;
      return;
    }
    int path = -1;
    for (int u = 0; u < static_cast<int>(g.size()) && path == -1; ++u) {
      if (used[u]) {
        for (auto [w, e] : g[u]) {
          if (comp[w] == v && state[e] == 0) {
            path = e;
            break;
          }
        }
      }
    }
    std::cout << "CLEAR " << path + 1 << std::endl;
    std::string answer;
    std::cin >> answer;
    state[path] = 1;
  }
}

int main() {
  std::ios_base::sync_with_stdio(false);
  std::cin.tie(nullptr);
  ReadMap();
  int start = entrance;
  Contract();
  BuildMasks();
  BuildConn();
  BuildDp();
  Explore(start);
  return 0;
}
