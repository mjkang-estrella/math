// Enumerate all twin-free pieces with threads of length <= L and exactly n vertices.
// A piece: tree, leaves have status f, internal vertices status n.
// Twin-free: no vertex has two isomorphic branches.  Rooted at the centre (or at the central
// edge), this holds iff at every vertex the child subtrees are pairwise non-isomorphic
// (branches pointing towards the centre are strictly higher than the child subtrees).
// Thread length: maximal path whose interior vertices have degree 2; length <= L means
// at most L-1 consecutive degree-2 vertices.
// Options: only pieces with at least one degree-2 vertex (others are covered by the
// Fokkink-Zandee theorem) and not paths.
// Output: "P n u1 v1 ..." lines.
// Usage: genpieces L n [count_only]
#include <bits/stdc++.h>
using namespace std;

struct RT {            // rooted tree (will hang from a parent)
    int size, height, top;  // top: length of the chain of single-child vertices starting at root
    int nch;             // number of children
    bool has2;           // contains a vertex of degree 2 (counting the root as having a parent)
    int off;             // children ids are pool[off .. off+nch-1], strictly increasing
};
vector<int> pool;
int NTOT;
vector<RT> T;
vector<vector<int>> bySize;
int L;

// enumerate strictly increasing sequences of ids from bySize lists with total size = rem
// ids are global indices; we order all trees by (size, index) = global id increasing.
void genChildren(int rem, int minId, vector<int>& cur, const function<void(vector<int>&)>& cb) {
    if (rem == 0) { cb(cur); return; }
    // choose next child with id >= minId and size <= rem
    for (int s = 1; s <= rem; s++) {
        const vector<int>& lst = bySize[s];
        // ids in lst are increasing; skip those < minId
        auto it = lower_bound(lst.begin(), lst.end(), minId);
        for (; it != lst.end(); ++it) {
            cur.push_back(*it);
            genChildren(rem - s, *it + 1, cur, cb);
            cur.pop_back();
        }
    }
}
// The above enumerates multisets in non-canonical order (sizes interleaved); to make the
// sequence strictly increasing in id we require ids increasing, and since ids are ordered by
// size first, choosing any next id > previous id is canonical.  We must restrict the loop to
// ids > previous; implemented via minId.  (Sizes of later children are >= earlier ones.)

void buildRooted(int N) {
    // global ids ordered by size
    T.clear(); bySize.assign(N + 1, {});
    // size 1: leaf
    T.push_back({1, 0, 0, 0, false, 0}); bySize[1].push_back(0);
    for (int s = 2; s <= N; s++) {
        vector<int> cur;
        // children total size s-1, children ids strictly increasing (distinct children)
        function<void(int, int)> rec = [&](int rem, int minId) {
            if (rem == 0) {
                RT r; r.size = s; r.nch = cur.size();
                r.height = 0; r.has2 = false;
                for (int c : cur) { r.height = max(r.height, T[c].height + 1); r.has2 |= T[c].has2; }
                if (r.size + r.height > NTOT - 1) return;   // cannot occur in a tree of order NTOT
                if (r.nch == 1) {
                    r.top = 1 + T[cur[0]].top;
                    if (r.top > L - 1) return;
                    r.has2 = true;
                } else r.top = 0;
                r.off = pool.size(); for (int c : cur) pool.push_back(c);
                T.push_back(r); bySize[s].push_back(T.size() - 1);
                return;
            }
            // next child: id >= minId, size <= rem.  ids ordered by size, so iterate sizes
            for (int cs = 1; cs <= rem; cs++) {
                if (cs >= s) break;
                const vector<int>& lst = bySize[cs];
                auto it = lower_bound(lst.begin(), lst.end(), minId);
                for (; it != lst.end(); ++it) {
                    cur.push_back(*it);
                    rec(rem - cs, *it + 1);
                    cur.pop_back();
                }
            }
        };
        rec(s - 1, 0);
    }
}

int nOut = 0;
long long cnt = 0;
bool countOnly = false;
vector<pair<int, int>> edges;
int nextV;
void emit(int id, int v) {
    for (int q = 0; q < T[id].nch; q++) { int c = pool[T[id].off + q]; int w = nextV++; edges.push_back({v, w}); emit(c, w); }
}
void output() {
    cnt++;
    if (countOnly) return;
    printf("P %d", nextV);
    for (auto& e : edges) printf(" %d %d", e.first, e.second);
    printf("\n");
}

int main(int argc, char** argv) {
    L = atoi(argv[1]); int n = atoi(argv[2]); countOnly = argc > 3 && atoi(argv[3]);
    NTOT = n;
    buildRooted(n);
    // unicentral: root with children set (distinct), >= 2 children of max height, total n-1
    {
        vector<int> cur;
        // emit(-1,0) special: root children = cur
        // implement by temporarily pushing a fake RT
        T.push_back({n, 0, 0, 0, false, 0});
        int fake = T.size() - 1;
        function<void(int, int)> rec2 = [&](int rem, int minId) {
            if (rem == 0) {
                int k = cur.size();
                if (k < 2) return;
                int H = -1, cntH = 0;
                for (int c : cur) { if (T[c].height > H) { H = T[c].height; cntH = 1; } else if (T[c].height == H) cntH++; }
                if (cntH < 2) return;
                bool has2 = false;
                for (int c : cur) has2 |= T[c].has2;
                if (k == 2) {
                    if (T[cur[0]].top + 1 + T[cur[1]].top > L - 1) return;
                    has2 = true;
                }
                if (!has2) return;
                bool path = (k == 2);
                if (path) for (int c : cur) { int x = c; while (T[x].nch == 1) x = pool[T[x].off]; if (T[x].nch != 0) path = false; }
                if (path) return;
                T[fake].off = pool.size(); T[fake].nch = cur.size(); for (int c : cur) pool.push_back(c);
                edges.clear(); nextV = 1; emit(fake, 0); output();
                pool.resize(T[fake].off);
                return;
            }
            for (int cs = 1; cs <= rem; cs++) {
                const vector<int>& lst = bySize[cs];
                auto it = lower_bound(lst.begin(), lst.end(), minId);
                for (; it != lst.end(); ++it) { cur.push_back(*it); rec2(rem - cs, *it + 1); cur.pop_back(); }
            }
        };
        rec2(n - 1, 0);
        T.pop_back();
    }
    // bicentral: two halves of sizes s <= n-s with equal height; unordered pair
    for (int s = 1; 2 * s <= n; s++) {
        const vector<int>& la = bySize[s];
        const vector<int>& lb = bySize[n - s];
        for (size_t i = 0; i < la.size(); i++)
            for (size_t j = (2 * s == n ? i : 0); j < lb.size(); j++) {
                int a = la[i], b = lb[j];
                if (T[a].height != T[b].height) continue;
                bool has2 = T[a].has2 || T[b].has2;
                int ca = (T[a].nch == 1) ? T[a].top : 0, cb = (T[b].nch == 1) ? T[b].top : 0;
                if (ca > 0 && cb > 0 && ca + cb > L - 1) continue;
                if (!has2) continue;
                bool path = true;
                for (int c : {a, b}) { int x = c; while (T[x].nch == 1) x = pool[T[x].off]; if (T[x].nch != 0) path = false; }
                if (path) continue;
                edges.clear(); nextV = 2; edges.push_back({0, 1});
                emit(a, 0); emit(b, 1); output();
            }
    }
    fprintf(stderr, "L=%d n=%d rooted=%zu pieces=%lld\n", L, n, T.size(), cnt);
}
