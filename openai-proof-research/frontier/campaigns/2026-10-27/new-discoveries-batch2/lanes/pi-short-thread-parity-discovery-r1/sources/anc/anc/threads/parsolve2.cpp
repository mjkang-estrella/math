// Strategy-certificate search for parity:  par(C) == true certifies g(C) == |E(C)| mod 2.
//   par(C) holds if
//     (A) for every move C -> D (a sum of components) there is a reply D -> D'' such that the
//         Grundy value of D'' is known (each component either has par()==true, value |E| mod 2,
//         or is small enough to be solved exactly) and equals |E(C)| mod 2; and
//     (B) if |E(C)| is odd, some move C -> D has known value 0.
//   By induction on |E|, (A) and (B) give g(C) = |E(C)| mod 2.  (Moves whose resulting value is
//   already known and != |E| mod 2 need no reply.)
// When par() fails for a piece, the exact solver is used as a fallback.
// Input: same as arrows ("P n edges" pieces, "T n edges" trees, "L ..." labelled).
// Output per line: g |E| method(par/exact)
#include "arrows.h"

Solver X;                 // exact solver (memo inside)
int EXACT_LIMIT = 12;     // components with at most this many edges are solved exactly
Memo parMemo;   // 128-bit key -> 1 true, 0 false
u64 parNodes = 0, exactCalls = 0;

static inline u64 kk(const Key& k) { return k.a ^ (k.b * 0x9E3779B97F4A7C15ULL); }

struct CK { Comp c; Key k; };

void movesOf(const Comp& C, vector<pair<int,int>>& mv) {
    int deg[MAXV]; for (int i = 0; i < C.n; i++) deg[i] = 0;
    for (int j = 0; j < C.E.size(); j++) { deg[C.E[j].first]++; deg[C.E[j].second]++; }
    mv.clear();
    for (int j = 0; j < C.E.size(); j++) for (int d = 0; d < 2; d++) {
        int t = d ? C.E[j].second : C.E[j].first, h = d ? C.E[j].first : C.E[j].second;
        if (Solver::canTail(C.lab[t], deg[t]) && Solver::canHead(C.lab[h], deg[h])) mv.push_back({j, d});
    }
}
void apply(const Comp& C, int j, int d, vector<CK>& out) {
    uint8_t lab2[MAXV]; for (int i = 0; i < C.n; i++) lab2[i] = C.lab[i];
    int t = d ? C.E[j].second : C.E[j].first, h = d ? C.E[j].first : C.E[j].second;
    lab2[t] = OUTA[lab2[t]]; lab2[h] = INA[lab2[h]];
    EdgeList E2; for (int q = 0; q < C.E.size(); q++) if (q != j) E2.push_back(C.E[q]);
    vector<Comp> parts; X.normalise(C.n, lab2, E2, parts);
    for (auto& P : parts) { vector<pair<Comp, Key>> r; X.canonAll(P, r); for (auto& q : r) out.push_back({q.first, q.second}); }
}

bool par(const Comp& C, const Key& k);

// known value of a component: par -> parity; small -> exact; else -1
int knownVal(const CK& c, bool allowPar) {
    int e = c.c.E.size();
    if (e <= EXACT_LIMIT) { exactCalls++; return X.grundyComp(const_cast<Comp&>(c.c), c.k); }
    int em = X.memo.get(c.k);
    if (em >= 0) return em;
    int pm = parMemo.get(c.k);
    if (pm >= 0) return pm ? (e & 1) : -1;
    if (!allowPar) return -1;
    return par(c.c, c.k) ? (e & 1) : -1;
}

bool par(const Comp& C, const Key& k) {
    int pm = parMemo.get(k);
    if (pm >= 0) return pm;
    parNodes++;
    int e = C.E.size();
    int target = e & 1;
    vector<pair<int,int>> mv; movesOf(C, mv);
    bool found0 = (target == 0);
    bool ok = true;
    for (auto& m1 : mv) {
        vector<CK> D; apply(C, m1.first, m1.second, D);
        // cheap evaluation of D without par recursion on big parts
        int x = 0; bool known = true;
        for (auto& c : D) { int v = knownVal(c, false); if (v < 0) { known = false; break; } x ^= v; }
        if (known) {
            if (x == target) { ok = false; break; }   // an option with the forbidden value
            if (x == 0) found0 = true;
            continue;
        }
        // search a reply.  Candidate replies are ordered heuristically:
        //   (1) results already fully known (memo) first, (2) then by size of largest component.
        bool replied = false;
        struct Cand { int score; size_t jj; vector<CK> R; };
        vector<Cand> cands;
        vector<int> otherKnown(D.size(), -2);
        for (size_t jj = 0; jj < D.size(); jj++) {
            vector<pair<int,int>> mv2; movesOf(D[jj].c, mv2);
            for (auto& m2 : mv2) {
                Cand cd; cd.jj = jj; apply(D[jj].c, m2.first, m2.second, cd.R);
                int mx = 0, unknown = 0;
                for (auto& c : cd.R) { mx = max(mx, (int)c.c.E.size()); if (c.c.E.size() > (size_t)EXACT_LIMIT && knownVal(c, false) < 0) unknown++; }
                for (size_t q = 0; q < D.size(); q++) if (q != jj) { mx = max(mx, (int)D[q].c.E.size()); }
                cd.score = (unknown ? 1000 : 0) + mx;
                cands.push_back(std::move(cd));
            }
        }
        sort(cands.begin(), cands.end(), [](const Cand& a, const Cand& b) { return a.score < b.score; });
        for (auto& cd : cands) {
            int y = 0; bool kr = true;
            for (size_t q = 0; q < D.size() && kr; q++) if (q != cd.jj) { int v = knownVal(D[q], true); if (v < 0) kr = false; else y ^= v; }
            if (!kr) continue;
            for (auto& c : cd.R) { int v = knownVal(c, true); if (v < 0) { kr = false; break; } y ^= v; }
            if (kr && y == target) { replied = true; break; }
        }
        if (!replied) { ok = false; break; }
    }
    if (ok && !found0) {
        // need an option of value 0: evaluate options with par recursion
        for (auto& m1 : mv) {
            vector<CK> D; apply(C, m1.first, m1.second, D);
            int x = 0; bool known = true;
            for (auto& c : D) { int v = knownVal(c, true); if (v < 0) { known = false; break; } x ^= v; }
            if (known && x == 0) { found0 = true; break; }
        }
        if (!found0) ok = false;
    }
    parMemo.put(k, ok ? 1 : 0);
    return ok;
}

int main(int argc, char** argv) {
    for (int i = 1; i < argc; i++) {
        string a = argv[i];
        if (a == "-limit" && i + 1 < argc) EXACT_LIMIT = atoi(argv[++i]);
    }
    string line;
    while (getline(cin, line)) {
        if (line.empty()) continue;
        istringstream in(line);
        string mode; in >> mode; int n; in >> n;
        uint8_t lab[MAXV]; vector<pair<int,int>> E;
        if (mode == "P") {
            E.resize(n - 1); for (auto& e : E) in >> e.first >> e.second;
            vector<int> deg(n, 0); for (auto& e : E) { deg[e.first]++; deg[e.second]++; }
            for (int i = 0; i < n; i++) lab[i] = deg[i] <= 1 ? SF : SN;
        } else if (mode == "L") {
            for (int i = 0; i < n; i++) { int s; in >> s; lab[i] = s; }
            int k; in >> k; E.resize(k); for (auto& e : E) in >> e.first >> e.second;
        } else continue;
        // normalise & canonicalise
        EdgeList EL; for (auto& e : E) EL.push_back(e);
        vector<Comp> parts; uint8_t l2[MAXV]; for (int i = 0; i < n; i++) l2[i] = lab[i];
        X.normalise(n, l2, EL, parts);
        int g = 0; bool allPar = true; int tot = 0;
        for (auto& P : parts) {
            vector<pair<Comp, Key>> r; X.canonAll(P, r);
            for (auto& q : r) {
                int e = q.first.E.size(); tot += e;
                int v;
                if (e <= EXACT_LIMIT) v = X.grundyComp(q.first, q.second), allPar = false;
                else if (par(q.first, q.second)) v = e & 1;
                else { v = X.grundyComp(q.first, q.second); allPar = false; }
                g ^= v;
            }
        }
        printf("%d %d %s\n", g, (int)E.size(), allPar ? "par" : "exact");
        fflush(stdout);
    }
    fprintf(stderr, "parNodes=%llu parMemo=%zu exactNodes=%llu exactMemo=%zu\n", (unsigned long long)parNodes, parMemo.used, (unsigned long long)X.nodes, X.memo.used);
}
