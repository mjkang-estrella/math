// Raw-rules Game of Arrows solver with a direct array memo (independent of all theory).
// Positions: each non-pendant edge is unmarked / tail->head as listed / reversed; encoded in base 3.
// Pendant edges are never marked (marking one makes its leaf a sink or source), but they are
// counted in the vertex incidence lists, so special vertices are handled by the raw rule.
// A move is legal iff afterwards neither endpoint is a sink or a source
// (all incident edges marked and all pointing in, resp. all pointing out).
// Input: one tree per line: "n u1 v1 ... u_{n-1} v_{n-1}".  Output: "g m".
// Memory: 3^m bytes (m <= 19).
#include <bits/stdc++.h>
using namespace std;
int n, m;
vector<int> mu, mv;                 // markable edges
vector<vector<pair<int,int>>> inc;  // per vertex: (markable edge index or -1 for pendant, +1 if vertex is head when state==1)
vector<uint64_t> pw;
vector<uint8_t> memo;
int st[64];

bool bad(int w) {
    bool anyIn = false, anyOut = false;
    for (auto& pr : inc[w]) {
        int e = pr.first;
        if (e < 0) return false;            // pendant edge: unmarked forever
        int s = st[e];
        if (s == 0) return false;
        // state 1: mu->mv ; state 2: mv->mu
        int head = (s == 1) ? mv[e] : mu[e];
        if (head == w) anyIn = true; else anyOut = true;
    }
    return !(anyIn && anyOut);
}
int grundy(uint64_t code) {
    if (memo[code] != 255) return memo[code];
    uint64_t seen = 0;
    for (int e = 0; e < m; e++) {
        if (st[e]) continue;
        for (int s = 1; s <= 2; s++) {
            st[e] = s;
            if (!bad(mu[e]) && !bad(mv[e])) {
                int g = grundy(code + s * pw[e]);
                seen |= 1ULL << g;
            }
            st[e] = 0;
        }
    }
    int g = 0; while ((seen >> g) & 1) g++;
    memo[code] = g;
    return g;
}
int main() {
    string line;
    while (getline(cin, line)) {
        if (line.empty()) continue;
        istringstream in(line);
        in >> n;
        vector<int> U(n - 1), V(n - 1), deg(n, 0);
        for (int i = 0; i < n - 1; i++) { in >> U[i] >> V[i]; deg[U[i]]++; deg[V[i]]++; }
        mu.clear(); mv.clear(); inc.assign(n, {});
        for (int i = 0; i < n - 1; i++) {
            if (deg[U[i]] > 1 && deg[V[i]] > 1) {
                int e = mu.size(); mu.push_back(U[i]); mv.push_back(V[i]);
                inc[U[i]].push_back({e, 0}); inc[V[i]].push_back({e, 1});
            } else { inc[U[i]].push_back({-1, 0}); inc[V[i]].push_back({-1, 0}); }
        }
        m = mu.size();
        if (m > 19) { printf("too many markable edges (%d)\n", m); continue; }
        pw.assign(m + 1, 1); for (int i = 1; i <= m; i++) pw[i] = pw[i - 1] * 3;
        memo.assign(pw[m], 255);
        for (int i = 0; i < m; i++) st[i] = 0;
        int g = grundy(0);
        printf("%d %d\n", g, m);
        fflush(stdout);
    }
}
