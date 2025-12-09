#include <bits/stdc++.h>

using namespace std;

const int MAXN = 300005;

const int MAXV = 1000005;

int divisors[MAXV];

long long sum[MAXN];

void add(int i, int x) {
  while (i < MAXN) {
    sum[i] += x;
    i += i & -i;
  }
}

long long query(int i) {
  long long res = 0;
  while (i > 0) {
    res += sum[i];
    i -= i & -i;
  }
  return res;
}

int main() {
  ios::sync_with_stdio(false);
  cin.tie(nullptr);

  for (int i = 1; i < MAXV; i++) {
    for (int j = i; j < MAXV; j += i) {
      divisors[j]++;
    }
  }

  int n, m;
  map<int, int> a;

  cin >> n >> m;

  for (int i = 1; i <= n; i++) {
    int x;
    cin >> x;
    add(i, x);
    if (x > 2) a[i] = x;
  }

  while (m--) {
    int op, l, r;
    cin >> op >> l >> r;
    if (op == 1) {
      auto it = a.lower_bound(l);
      while (it != a.end() && it->first <= r) {
        int idx = it->first;
        int val = it->second;
        if (divisors[val] != val) {
          add(idx, divisors[val] - val);
          it->second = divisors[val];
          ++it;
        } else {
          it = a.erase(it);
        }
      }
    } else {
      cout << query(r) - query(l - 1) << "\n";
    }
  }
}