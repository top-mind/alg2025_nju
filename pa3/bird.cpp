/*
  Each bird needs food that has weights greater than or equal to its demand
  How many birds can be satisfied?
  tag: greedy
 */
#include <bits/stdc++.h>
using namespace std;
int main() {
  int n, m;
  cin >> n >> m;
  vector<int> birds(n), foods(m);
  for (int i = 0; i < n; i++) cin >> birds[i];
  for (int i = 0; i < m; i++) cin >> foods[i];
  sort(birds.begin(), birds.end());
  sort(foods.begin(), foods.end());
  int i = 0, j = 0;
  while (i < n && j < m) {
    if (foods[j] >= birds[i]) {
      i++;
      j++;
    } else {
      j++;
    }
  }
  cout << i << "\n";
  return 0;
}