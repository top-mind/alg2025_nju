/* Given a weighted undirected graph, find the bottleneck weight that
   edges with weight less than or equal to it connect all the nodes.
   If not all nodes can be connected, return -1.
   tag: union-find, greedy, kruskal
 */
#include <bits/stdc++.h>
using namespace std;

struct DSU {
  vector<int> p, r;
  DSU(int n) : p(n + 1), r(n + 1) {
    for (int i = 0; i <= n; i++) p[i] = i;
  }
  int find(int x) {
    if (p[x] != x) p[x] = find(p[x]);
    return p[x];
  }
  bool unite(int x, int y) {
    int rx = find(x), ry = find(y);
    if (rx == ry) return false;
    if (r[rx] < r[ry]) {
      p[rx] = ry;
    } else if (r[rx] > r[ry]) {
      p[ry] = rx;
    } else {
      p[ry] = rx;
      r[rx]++;
    }
    return true;
  }
};

int main() {
  ios::sync_with_stdio(false);
  cin.tie(nullptr);
  int n, m;
  cin >> n >> m;
  vector<tuple<int, int, int>> edges(m);
  for (int i = 0; i < m; i++) {
    int u, v, w;
    cin >> u >> v >> w;
    edges[i] = {w, u, v};
  }
  sort(edges.begin(), edges.end());
  DSU dsu(n);
  int components = n;
  int bottleneck = -1;
  for (const auto& [w, u, v] : edges) {
    if (dsu.unite(u, v)) {
      components--;
      bottleneck = w;
      if (components == 1) break;
    }
  }
  if (components > 1) bottleneck = -1;
  cout << bottleneck << "\n";
}