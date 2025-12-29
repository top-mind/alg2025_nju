/* Count how many permutations that the neighbors of each element has difference greater than k.
   tag: dp, bitmask
 */
#include <bits/stdc++.h>
using namespace std;
int main() {
  ios::sync_with_stdio(false);
  cin.tie(0);
  int n, k;
  cin >> n >> k;
  vector<int> a(n);
  for (int i = 0; i < n; i++) {
    cin >> a[i];
  }
  vector<vector<long long>> dp(1 << n, vector<long long>(n, 0));
  for (int i = 0; i < n; i++) {
    dp[1 << i][i] = 1;
  }
  for (int mask = 1; mask < (1 << n); mask++) {
    for (int u = 0; u < n; u++) {
      if (!((mask >> u) & 1)) continue;
      for (int v = 0; v < n; v++) {
        if ((mask >> v) & 1) continue;
        if (abs(a[u] - a[v]) > k) {
          dp[mask | (1 << v)][v] += dp[mask][u];
        }
      }
    }
  }
  long long ans = 0;
  for (int i = 0; i < n; i++) {
    ans += dp[(1 << n) - 1][i];
  }
  cout << ans << "\n";

  return 0;
}