// Validate the explicit strategy of the proof of the "C2 theorem" (threads <= 2).
// Class K = C2 u D1 u {single edges}:
//   C2 : all leaves f, no edge joins two vertices of degree 2.
//   D1a: exactly one non-f leaf w (status i/o); its neighbour has degree >= 3; no edge joins two
//        degree-2 vertices.
//   D1b: all leaves f; a vertex w of degree 2 and status i/o lies on every edge joining two
//        degree-2 vertices.
// For every K position P (enumerated) and every legal first move, apply Bob's rule from the proof
// (or no reply), normalise (dead edges, rule N4, f-splitting; NO twin reduction) and check that the
// result is a sum of K components whose total number of edges is |E(P)|-1 (no reply) or |E(P)|-2.
// Also check (B): from a D1 position, the "neutralising" move at w gives a K-sum.
#include "arrows.h"

Solver S;
struct Pos { int n; uint8_t lab[MAXV]; vector<pair<int,int>> E; };

void degs(const Pos& P, vector<int>& d) { d.assign(P.n, 0); for (auto& e : P.E) { d[e.first]++; d[e.second]++; } }

// K membership of a single normalised component
bool inK(const Comp& C) {
    int n = C.n, m = C.E.size();
    if (m <= 1) return true;
    int deg[MAXV], nb[MAXV];
    for (int i = 0; i < n; i++) deg[i] = 0;
    for (auto& e : C.E) { deg[e.first]++; deg[e.second]++; }
    for (auto& e : C.E) { nb[e.first] = e.second; nb[e.second] = e.first; }
    int nbad = 0, bl = -1;
    for (int i = 0; i < n; i++) if (deg[i] == 1 && C.lab[i] != SF) { nbad++; bl = i; }
    vector<pair<int,int>> ch;
    for (auto& e : C.E) if (deg[e.first] == 2 && deg[e.second] == 2) ch.push_back(e);
    if (nbad == 0 && ch.empty()) return true;
    if (nbad > 1) return false;
    if (nbad == 1) return ch.empty() && deg[nb[bl]] >= 3;                // D1a
    // D1b: a common vertex of all chain edges with degree 2 and status i/o
    for (int w : {ch[0].first, ch[0].second}) {
        if (C.lab[w] != SI && C.lab[w] != SO) continue;
        bool ok = true; for (auto& e : ch) if (e.first != w && e.second != w) ok = false;
        if (ok) return true;
    }
    return false;
}

// play a sequence of moves (tail,head) on P, normalise, return components
bool playAndCheck(const Pos& P, const vector<pair<int,int>>& mv, int expectEdges, string& why) {
    Pos Q = P;
    for (auto& m : mv) {
        vector<int> d; degs(Q, d);
        int t = m.first, h = m.second;
        int idx = -1;
        for (int j = 0; j < Q.E.size(); j++) if ((Q.E[j].first == t && Q.E[j].second == h) || (Q.E[j].first == h && Q.E[j].second == t)) idx = j;
        if (idx < 0) { why = "edge not present"; return false; }
        if (!Solver::canTail(Q.lab[t], d[t]) || !Solver::canHead(Q.lab[h], d[h])) { why = "illegal move"; return false; }
        Q.lab[t] = OUTA[Q.lab[t]]; Q.lab[h] = INA[Q.lab[h]];
        Q.E.erase(Q.E.begin() + idx);
    }
    EdgeList EL; for (auto& e : Q.E) EL.push_back(e);
    vector<Comp> parts; uint8_t l2[MAXV]; for (int i = 0; i < Q.n; i++) l2[i] = Q.lab[i];
    S.normalise(Q.n, l2, EL, parts);
    int tot = 0;
    for (auto& C : parts) { tot += C.E.size(); if (!inK(C)) { why = "component not in K"; return false; } }
    if (tot != expectEdges) { why = "edge count " + to_string(tot) + " != " + to_string(expectEdges); return false; }
    return true;
}

// does the branch at a through neighbour r contain vertex w ?
bool branchHas(const Pos& P, int a, int r, int w) {
    vector<vector<int>> adj(P.n);
    for (auto& e : P.E) { adj[e.first].push_back(e.second); adj[e.second].push_back(e.first); }
    vector<int> st = {r}; vector<char> seen(P.n, 0); seen[a] = seen[r] = 1;
    while (!st.empty()) { int x = st.back(); st.pop_back(); if (x == w) return true; for (int y : adj[x]) if (!seen[y]) { seen[y] = 1; st.push_back(y); } }
    return false;
}
// component (of P) containing x after deleting edge (u,v)
bool sameSide(const Pos& P, int u, int v, int x, int target) {
    vector<vector<int>> adj(P.n);
    for (auto& e : P.E) if (!((e.first == u && e.second == v) || (e.first == v && e.second == u))) { adj[e.first].push_back(e.second); adj[e.second].push_back(e.first); }
    vector<int> st = {x}; vector<char> seen(P.n, 0); seen[x] = 1;
    while (!st.empty()) { int y = st.back(); st.pop_back(); if (y == target) return true; for (int z : adj[y]) if (!seen[z]) { seen[z] = 1; st.push_back(z); } }
    return false;
}
static inline int typeAt(int x, int t, int h) { return x == t ? SO : SI; }   // status contribution
static inline int opp(int s) { return s == SI ? SO : SI; }
// orientation giving vertex x an arc of type ty (SI = into x) on edge x-y
static inline pair<int,int> arcWithType(int x, int y, int ty) { return ty == SI ? make_pair(y, x) : make_pair(x, y); }

long long nPos = 0, nMoves = 0, nReplies = 0, nFail = 0, nValFail = 0;
bool VALUES = false;

void report(const Pos& P, pair<int,int> m1, const string& why, const char* tag) {
    nFail++;
    if (nFail > 15) return;
    printf("FAIL[%s] %s labels=", tag, why.c_str());
    for (int v = 0; v < P.n; v++) printf("%c", "niof"[P.lab[v]]);
    printf(" edges="); for (auto& e : P.E) printf(" %d-%d", e.first, e.second);
    printf(" move %d->%d\n", m1.first, m1.second);
}

void checkPos(const Pos& P) {
    vector<int> d; degs(P, d);
    int n = P.n, e = P.E.size();
    // classify
    Comp C; C.n = n; for (int i = 0; i < n; i++) C.lab[i] = P.lab[i]; for (auto& x : P.E) C.E.push_back(x);
    if (!inK(C)) return;
    nPos++;
    if (VALUES) {
        vector<pair<int,int>> EE = P.E; uint8_t lb[MAXV]; for (int i = 0; i < n; i++) lb[i] = P.lab[i];
        int g = S.grundyForest(n, lb, EE);
        if (g != (e & 1)) { nValFail++; if (nValFail <= 5) { printf("VALUE FAIL g=%d e=%d labels=", g, e); for (int v = 0; v < n; v++) printf("%c", "niof"[P.lab[v]]); printf("\n"); } }
    }
    // find designated w (if not C2)
    int w = -1; bool isC2 = true; int kind = 0;
    for (int i = 0; i < n; i++) if (d[i] == 1 && P.lab[i] != SF) { w = i; isC2 = false; kind = 1; }
    if (isC2) {
        for (auto& x : P.E) if (d[x.first] == 2 && d[x.second] == 2) { isC2 = false; }
        if (!isC2) {
            vector<pair<int,int>> ch; for (auto& x : P.E) if (d[x.first] == 2 && d[x.second] == 2) ch.push_back(x);
            for (int c : {ch[0].first, ch[0].second}) {
                if (P.lab[c] != SI && P.lab[c] != SO) continue;
                bool ok = true; for (auto& x : ch) if (x.first != c && x.second != c) ok = false;
                if (ok) { w = c; break; }
            }
            kind = 2;
        }
    }
    if (e <= 1) return;
    vector<int> nbw;
    if (w >= 0) for (auto& x : P.E) { if (x.first == w) nbw.push_back(x.second); if (x.second == w) nbw.push_back(x.first); }
    // (B): neutralising move at w
    if (!isC2) {
        pair<int,int> mb;
        if (kind == 1) { int y = nbw[0]; mb = (P.lab[w] == SI) ? make_pair(w, y) : make_pair(y, w); }
        else { int x = nbw[0]; mb = arcWithType(w, x, opp(P.lab[w])); }
        string why;
        if (!playAndCheck(P, {mb}, e - 1, why)) report(P, mb, why, "B");
    }
    for (int j = 0; j < e; j++) for (int dd = 0; dd < 2; dd++) {
        int t = dd ? P.E[j].second : P.E[j].first, h = dd ? P.E[j].first : P.E[j].second;
        if (!Solver::canTail(P.lab[t], d[t]) || !Solver::canHead(P.lab[h], d[h])) continue;
        nMoves++;
        pair<int,int> m1 = {t, h};
        vector<pair<int,int>> reply;   // empty = no reply
        if (!isC2) {
            if (t == w || h == w) {
                // II.1
                if (kind == 2) {
                    int x = (t == w) ? h : t;
                    int tyw = typeAt(w, t, h);
                    if (P.lab[w] == tyw) {        // w becomes a blocked leaf at y
                        int y = (nbw[0] == x) ? nbw[1] : nbw[0];
                        if (d[y] == 2) {
                            // forced edge w-y: w (status tyw) needs the opposite type
                            reply.push_back(arcWithType(w, y, opp(tyw)));
                        }
                    }
                }
            } else {
                // II.2: a = endpoint on w's side
                int a;
                if (sameSide(P, t, h, t, w)) a = t; else a = h;
                int tau = typeAt(a, t, h);
                int other = (a == t) ? h : t;
                int sa = P.lab[a];
                bool becomesF = (sa == SI && tau == SO) || (sa == SO && tau == SI);
                if (!becomesF) {
                    int dn = d[a] - 1;
                    vector<int> rem; for (auto& x : P.E) { if (x.first == a && x.second != other) rem.push_back(x.second); if (x.second == a && x.first != other) rem.push_back(x.first); }
                    if (dn == 2) {
                        bool isY = (kind == 1 && nbw[0] == a);
                        bool chainBad = false;
                        for (int c : rem) if (c != w && d[c] == 2) chainBad = true;
                        if (isY || chainBad) {
                            bool n4 = false;
                            if (isY) { int pend = (P.lab[w] == SI) ? SI : SO; /* w status i -> w->a: a gets in */ if (pend != tau) n4 = true; }
                            if (!n4) {
                                int r = -1;
                                for (int c : rem) if (c != w && !branchHas(P, a, c, w)) { r = c; break; }
                                if (r < 0) { report(P, m1, "no r", "rule"); continue; }
                                reply.push_back(arcWithType(a, r, opp(tau)));
                            }
                        }
                    } else if (dn == 1) {
                        int z = rem[0];
                        // pending: a (status tau) needs opposite type: z gets type pi
                        int pi = (tau == SO) ? SO : SI;   // a has out-arc -> edge must be z->a -> z gets out
                        if (z == w) {
                            if (P.lab[w] == pi) {
                                int x = (nbw[0] == a) ? nbw[1] : nbw[0];
                                reply.push_back(arcWithType(w, x, opp(pi)));
                            }
                        } else {
                            if (P.lab[z] != opp(pi)) {
                                int q = -1;
                                vector<int> nz; for (auto& x : P.E) { if (x.first == z) nz.push_back(x.second); if (x.second == z) nz.push_back(x.first); }
                                for (int c : nz) if (c != a && c != w && !branchHas(P, z, c, w)) { q = c; break; }
                                if (q < 0) { report(P, m1, "no q", "rule"); continue; }
                                reply.push_back(arcWithType(z, q, opp(pi)));
                            }
                        }
                    }
                }
            }
        }
        vector<pair<int,int>> seq = {m1};
        for (auto& r : reply) seq.push_back(r);
        if (!reply.empty()) nReplies++;
        string why;
        if (!playAndCheck(P, seq, e - (int)seq.size(), why)) report(P, m1, why + (reply.empty() ? " [no reply]" : " [reply]"), "A");
    }
}

int main(int argc, char** argv) {
    if (argc > 1 && string(argv[1]) == "-values") VALUES = true;
    string line;
    while (getline(cin, line)) {
        istringstream in(line); int n; in >> n; if (n < 3) continue;
        vector<pair<int,int>> E(n - 1); for (auto& e : E) in >> e.first >> e.second;
        vector<int> deg(n, 0); for (auto& e : E) { deg[e.first]++; deg[e.second]++; }
        int chain = 0; for (auto& e : E) if (deg[e.first] == 2 && deg[e.second] == 2) chain++;
        if (chain > 2) continue;
        vector<int> leaves, internal;
        for (int v = 0; v < n; v++) (deg[v] == 1 ? leaves : internal).push_back(v);
        int k = internal.size(); long long totI = 1; for (int i = 0; i < k; i++) totI *= 3;
        int L = leaves.size();
        for (int bl = -1; bl < L; bl++) for (int bs = 0; bs < (bl < 0 ? 1 : 2); bs++)
        for (long long code = 0; code < totI; code++) {
            Pos P; P.n = n; P.E = E;
            for (int v : leaves) P.lab[v] = SF;
            if (bl >= 0) P.lab[leaves[bl]] = bs ? SO : SI;
            long long c = code; for (int i = 0; i < k; i++) { P.lab[internal[i]] = c % 3; c /= 3; }
            checkPos(P);
        }
    }
    printf("K positions=%lld moves=%lld replies=%lld failures=%lld value-failures=%lld\n", nPos, nMoves, nReplies, nFail, nValFail);
}
