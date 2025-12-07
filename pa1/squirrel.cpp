#include <bits/stdc++.h>

using namespace std;

int main() {
  int T;
  cin >> T;
  while (T--) {
    int n;
    cin >> n;
    vector<int> a(n);
    int l = 0, r = n - 1;
    for (int i = 0; i < n; i++) cin >> a[i];
    int i;
    for (i = 1; i <= n; i ++) {
      if (a[l] == i) l++;
      else if (a[r] == i) r--;
      else break;
    }
    if (i == n + 1) {
      cout << "YES" << endl;
    } else {
      cout << "NO" << endl;
    }
  }
  return 0;
}