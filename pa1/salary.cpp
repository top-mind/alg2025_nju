#include <bits/stdc++.h>

using namespace std;

int main() {
  int n, m;
  cin >> n >> m;
  vector<int> a(n);
  int l = 0, r = 0;
  for (int i = 0; i < n; i++) {
    cin >> a[i];
    r += a[i];
    l = max(l, a[i]);
  }

  auto check = [&](int mid) -> bool {
    int seg = 1, tot = 0;
    for (int i = 0; i < n; i++) {
      tot += a[i];
      if (tot > mid) {
        seg++;
        tot = a[i];
      }
    }
    return (seg <= m);
  };

  while (l < r) {
    int mid = l + (r - l) / 2;
    if (check(mid)) {
      r = mid;
    } else {
      l = mid + 1;
    }
  }
  cout << l << endl;
  return 0;
}