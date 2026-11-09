// Free-tree generator (Wright-Richmond-Odlyzko-McKay via level sequences, Beyer-Hedetniemi successor),
// ported from the algorithm description used in networkx.nonisomorphic_trees.
#pragma once
#include <vector>
#include <utility>
#include <algorithm>

static bool nextRooted(std::vector<int>& pred, int p = -1) {
  if (p < 0) { p = pred.size() - 1; while (pred[p] == 1) p--; }
  if (p == 0) return false;
  int q = p - 1; while (pred[q] != pred[p] - 1) q--;
  for (size_t i = p; i < pred.size(); i++) pred[i] = pred[i - p + q];
  return true;
}
static void splitTree(const std::vector<int>& L, std::vector<int>& left, std::vector<int>& rest) {
  bool one = false; size_t m = L.size();
  for (size_t i = 0; i < L.size(); i++) if (L[i] == 1) { if (one) { m = i; break; } else one = true; }
  left.clear(); rest.clear();
  for (size_t i = 1; i < m; i++) left.push_back(L[i] - 1);
  rest.push_back(0); for (size_t i = m; i < L.size(); i++) rest.push_back(L[i]);
}
static bool nextTree(std::vector<int>& cand) {
  std::vector<int> left, rest; splitTree(cand, left, rest);
  int lh = *std::max_element(left.begin(), left.end()), rh = *std::max_element(rest.begin(), rest.end());
  bool valid = rh >= lh;
  if (valid && rh == lh) {
    if (left.size() > rest.size()) valid = false;
    else if (left.size() == rest.size() && left > rest) valid = false;
  }
  if (valid) return true;
  int p = left.size();
  std::vector<int> nc = cand;
  if (!nextRooted(nc, p)) return false;
  if (cand[p] > 2) {
    std::vector<int> nl, nr; splitTree(nc, nl, nr);
    int nlh = *std::max_element(nl.begin(), nl.end());
    int len = nlh + 1;
    for (int k = 0; k < len; k++) nc[nc.size() - len + k] = k + 1;
  }
  cand = nc;
  return true;
}
static void layoutEdges(const std::vector<int>& L, std::vector<std::pair<int,int>>& E) {
  E.clear(); std::vector<int> st;
  for (size_t i = 0; i < L.size(); i++) {
    if (!st.empty()) { while (L[st.back()] >= L[i]) st.pop_back(); E.push_back({(int)i, st.back()}); }
    st.push_back(i);
  }
}
// calls f(n, edges) for each free tree of order n (n >= 2)
template <class F> static void forEachTree(int n, F f) {
  std::vector<int> L;
  for (int i = 0; i <= n / 2; i++) L.push_back(i);
  for (int i = 1; i < (n + 1) / 2; i++) L.push_back(i);
  std::vector<std::pair<int,int>> E;
  while (true) {
    if (!nextTree(L)) break;
    layoutEdges(L, E); f(n, E);
    if (!nextRooted(L)) break;
  }
}
