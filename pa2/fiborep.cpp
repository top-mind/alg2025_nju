#include <bits/stdc++.h>

using namespace std;

vector<long long> a;

const long long maxc = 1000000000000ll;

int main() {
  a.push_back(1);
  a.push_back(2);
  int n = 2;
  while (a[n - 1] < maxc) {
    a.push_back(a[n - 2] + a[n - 1]);
    n++;
  }
  long long m;
  cin >> m;
  vector<int> b;
  while (a[--n] > m)
    ;
  m -= a[n]; int cnt = 0;
  for (--n; n >= 0; n--) {
    if (a[n] <= m) {
      m -= a[n];
      b.push_back(cnt);
      cnt = 0;
    } else {
      cnt++;
    }
  }
  b.push_back(cnt);
  long long n1 = 1, n2 = 0;
  for (int i = (int) b.size() - 1; i >= 0; i--) {
    long long n1p = n1 + n2;
    n2 = (b[i] / 2) * n1 + (b[i] + 1) / 2 * n2;
    n1 = n1p;
  }
  cout << n1 + n2 << endl;
  return 0;
}