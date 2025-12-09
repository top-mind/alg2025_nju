#include <bits/stdc++.h>

using namespace std;

struct DSU {
  vector<int> p;
  vector<int> r;
  DSU(int n) : p(n), r(n) {
    iota(p.begin(), p.end(), 0);
  }
  int find(int x) {
    if (p[x] == x) return x;
    return p[x] = find(p[x]);
  }
  void unite(int x, int y) {
    int px = find(x), py = find(y);
    if (px == py) return;
    if (r[px] < r[py]) {
      p[px] = py;
    } else if (r[px] > r[py]) {
      p[py] = px;
    } else {
      p[py] = px;
      r[px]++;
    }
  }
  bool same(int x, int y) {
    return find(x) == find(y);
  }
};

int main() {
  int n, m1, m2;
  cin >> n >> m1 >> m2;
  DSU dsu1(n), dsu2(n);
  while (m1--) {
    int x, y;
    cin >> x >> y;
    dsu1.unite(x - 1, y - 1);
  }
  while (m2--) {
    int x, y;
    cin >> x >> y;
    dsu2.unite(x - 1, y - 1);
  }
  queue<int> s1, s2; vector<pair<int, int>> ans;
  for (int i = 1; i < n; i++) {
    bool b1 = dsu1.same(0, i);
    bool b2 = dsu2.same(0, i);
    if (!b1 && !b2) {
      ans.emplace_back(1, i + 1);
      dsu1.unite(0, i);
      dsu2.unite(0, i);
    } else if (b1 && !b2) {
      s1.push(i);
    } else if (!b1 && b2) {
      s2.push(i);
    }
  }
  while (s1.size() && s2.size()) {
    while (s1.size() && dsu2.same(0, s1.front())) s1.pop();
    while (s2.size() && dsu1.same(0, s2.front())) s2.pop();
    if (s1.empty() || s2.empty()) break;

    int x = s1.front(); s1.pop();
    int y = s2.front(); s2.pop();

    dsu1.unite(x, y);
    dsu2.unite(x, y);
    if (x > y) swap(x, y);
    ans.emplace_back(x + 1, y + 1);
  }

  cout << ans.size() << "\n";
  for (auto [x, y] : ans) {
    cout << x << " " << y << "\n";  
  }
}