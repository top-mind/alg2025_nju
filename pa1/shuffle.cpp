#include <bits/stdc++.h>

using namespace std;

int main() {
  int n;
  cin >> n;
  vector<int> a(n);
  for (int i = 0; i < n; i++) cin >> a[i];

  if (n == 1) {
    cout << 0 << endl;
    return 0;
  }

  sort(a.begin(), a.end());

  for (int i = 0; i < n - 1; i++) a[i] = a[i + 1] - a[i];

  long long ans = 0;
  for (int i = 0; i < (n - 1) / 2; i++) {
    ans += 2ll * (i + 1) * (a[i] + a[n - i - 2]);
  }
  if (n & 1) {
    ans -= min(a[n / 2 - 1], a[n / 2]);
  } else {
    ans += ((long long)(n - 1)) * a[n / 2 - 1];
  }
  cout << ans << endl;
  return 0;
}