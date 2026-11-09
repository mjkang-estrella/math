// Syntactic strategy check for a class D of status-labelled trees (no Grundy values used).
// D (parametrised):
//   (D1) no two adjacent vertices of degree 2 (any status)            [chain<=1]
//   (D2) all leaves f, except at most `maxb` blocked leaves (status i/o), each adjacent to a
//        vertex of degree >= 3
//   single-edge trees are always in D.
// Conditions checked for every P in D (enumerated over all trees with n vertices, all labellings):
//   (A) every move P->P' with P' not a D-sum has a reply P'->P'' with P'' a D-sum and
//       |E(P'')| == |E(P)| (mod 2)
//   (B) if |E(P)| odd, some move P->P' gives a D-sum.
// If (A),(B) hold for all P in D and every D-tree satisfies parity... (by induction (A),(B) imply parity).
// Usage: dcheck maxb maxex < trees
#include "arrows.h"

int MAXB;
bool TWIN = true;

// class K = C2 u D1 u single edges.
//   C2: all leaves f, no two adjacent degree-2 vertices.
//   D1: exists w with status i/o such that: all leaves other than w are f; every edge joining two
//       degree-2 vertices contains w; if w is a leaf, its neighbour has degree >= 3.
int MODE = 1;   // 0: C2 only, 1: C2 u D1
bool inD(const Comp& C) {
    int n = C.n, m = C.E.size();
    if (m <= 1) return true;
    int deg[MAXV]; int nb[MAXV];
    for (int i = 0; i < n; i++) deg[i] = 0;
    for (int j = 0; j < m; j++) { deg[C.E[j].first]++; deg[C.E[j].second]++; }
    for (int j = 0; j < m; j++) { nb[C.E[j].first] = C.E[j].second; nb[C.E[j].second] = C.E[j].first; }
    // candidates for w: vertices forced by violations
    int badLeaf = -1, nBadLeaf = 0;
    for (int i = 0; i < n; i++) if (deg[i] == 1 && C.lab[i] != SF) { nBadLeaf++; badLeaf = i; }
    vector<int> chainEdges;
    for (int j = 0; j < m; j++) if (deg[C.E[j].first] == 2 && deg[C.E[j].second] == 2) chainEdges.push_back(j);
    if (nBadLeaf == 0 && chainEdges.empty()) return true;           // C2
    if (MODE == 0) return false;
    if (nBadLeaf > 1) return false;
    vector<int> cand;
    if (nBadLeaf == 1) cand.push_back(badLeaf);
    else { int j = chainEdges[0]; cand.push_back(C.E[j].first); cand.push_back(C.E[j].second); }
    for (int w : cand) {
        if (C.lab[w] != SI && C.lab[w] != SO) continue;
        bool ok = true;
        for (int j : chainEdges) if (C.E[j].first != w && C.E[j].second != w) { ok = false; break; }
        if (!ok) continue;
        if (deg[w] == 1 && deg[nb[w]] < 3) continue;
        return true;
    }
    return false;
}

Solver S;

// apply a move on component C (edge index ei, direction d) -> components
void applyMove(const Comp& C, int ei, int d, vector<Comp>& out) {
    int n = C.n;
    uint8_t lab2[MAXV];
    for (int i = 0; i < n; i++) lab2[i] = C.lab[i];
    int t = d ? C.E[ei].second : C.E[ei].first, h = d ? C.E[ei].first : C.E[ei].second;
    lab2[t] = OUTA[lab2[t]]; lab2[h] = INA[lab2[h]];
    EdgeList E2;
    for (int j = 0; j < C.E.size(); j++) if (j != ei) E2.push_back(C.E[j]);
    vector<Comp> tmp;
    S.normalise(n, lab2, E2, tmp);
    if (!TWIN) { out = tmp; return; }
    for (auto& X : tmp) {
        vector<pair<Comp, Key>> r;
        S.canonAll(X, r);
        for (auto& q : r) out.push_back(q.first);
    }
}
bool legal(const Comp& C, int ei, int d, int* deg) {
    int t = d ? C.E[ei].second : C.E[ei].first, h = d ? C.E[ei].first : C.E[ei].second;
    return Solver::canTail(C.lab[t], deg[t]) && Solver::canHead(C.lab[h], deg[h]);
}

int main(int argc, char** argv) {
    MAXB = atoi(argv[1]); MODE = MAXB;
    int maxex = argc > 2 ? atoi(argv[2]) : 10;
    for (int i = 3; i < argc; i++) if (string(argv[i]) == "-notwin") TWIN = false;
    string line;
    long long tot = 0, failA = 0, failB = 0;
    while (getline(cin, line)) {
        istringstream in(line);
        int n; in >> n; if (n < 3) continue;
        vector<pair<int, int>> E(n - 1);
        for (auto& e : E) in >> e.first >> e.second;
        vector<int> deg(n, 0);
        for (auto& e : E) { deg[e.first]++; deg[e.second]++; }
        int chainCnt = 0;
        for (auto& e : E) if (deg[e.first] == 2 && deg[e.second] == 2) chainCnt++;
        if (chainCnt > 2) continue;
        vector<int> leaves, internal;
        for (int v = 0; v < n; v++) (deg[v] == 1 ? leaves : internal).push_back(v);
        int k = internal.size();
        long long totalI = 1; for (int i = 0; i < k; i++) totalI *= 3;
        // leaves: f, or blocked (i/o) for at most MAXB of them
        int L = leaves.size();
        vector<vector<int>> leafAssign;  // each: per leaf status
        {
            vector<int> cur(L, SF);
            function<void(int, int)> rec = [&](int idx, int used) {
                if (idx == L) { leafAssign.push_back(cur); return; }
                cur[idx] = SF; rec(idx + 1, used);
                if (used < 1) { cur[idx] = SI; rec(idx + 1, used + 1); cur[idx] = SO; rec(idx + 1, used + 1); cur[idx] = SF; }
            };
            rec(0, 0);
        }
        for (auto& la : leafAssign)
        for (long long code = 0; code < totalI; code++) {
            Comp C; C.n = n;
            for (int i = 0; i < L; i++) C.lab[leaves[i]] = la[i];
            long long c = code;
            for (int i = 0; i < k; i++) { C.lab[internal[i]] = c % 3; c /= 3; }
            for (auto& e : E) C.E.push_back(e);
            if (!inD(C)) continue;
            tot++;
            int m = C.E.size();
            int dg[MAXV]; for (int i = 0; i < n; i++) dg[i] = deg[i];
            bool okB = (m % 2 == 0);
            bool okA = true;
            for (int ei = 0; ei < m && okA; ei++) for (int d = 0; d < 2; d++) {
                if (!legal(C, ei, d, dg)) continue;
                vector<Comp> comps; applyMove(C, ei, d, comps);
                bool all = true; for (auto& X : comps) if (!inD(X)) { all = false; break; }
                if (all) { okB = true; continue; }
                bool found = false;
                for (size_t j = 0; j < comps.size() && !found; j++) {
                    bool othersOk = true; int otherE = 0;
                    for (size_t q = 0; q < comps.size(); q++) if (q != j) { if (!inD(comps[q])) othersOk = false; otherE += comps[q].E.size(); }
                    if (!othersOk) continue;
                    Comp& X = comps[j];
                    int dx[MAXV]; for (int i = 0; i < X.n; i++) dx[i] = 0;
                    for (auto& e : X.E) { dx[e.first]++; dx[e.second]++; }
                    for (int e2 = 0; e2 < X.E.size() && !found; e2++) for (int d2 = 0; d2 < 2 && !found; d2++) {
                        if (!legal(X, e2, d2, dx)) continue;
                        vector<Comp> c2; applyMove(X, e2, d2, c2);
                        int tE = otherE; bool ok2 = true;
                        for (auto& Y : c2) { if (!inD(Y)) { ok2 = false; break; } tE += Y.E.size(); }
                        if (ok2 && (tE % 2) == (m % 2)) found = true;
                    }
                }
                if (!found) {
                    okA = false;
                    if (failA < maxex) {
                        printf("A-fail: labels=");
                        for (int v = 0; v < n; v++) printf("%c", "nio f"[C.lab[v] == SF ? 4 : C.lab[v]]);
                        printf(" edges="); for (auto& e : E) printf(" %d-%d", e.first, e.second);
                        int t = d ? E[ei].second : E[ei].first, h = d ? E[ei].first : E[ei].second;
                        printf("  move %d->%d\n", t, h);
                    }
                    break;
                }
            }
            if (!okA) failA++;
            if (!okB) {
                failB++;
                if (failB <= maxex) {
                    printf("B-fail: labels=");
                    for (int v = 0; v < n; v++) printf("%c", "nio f"[C.lab[v] == SF ? 4 : C.lab[v]]);
                    printf(" edges="); for (auto& e : E) printf(" %d-%d", e.first, e.second);
                    printf("\n");
                }
            }
        }
    }
    printf("maxb=%d D-positions=%lld A-fail=%lld B-fail=%lld\n", MAXB, tot, failA, failB);
}
