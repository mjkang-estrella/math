// Independent solver for the Game of Arrows on spiders with any number of legs.
// Written separately from spider3.cpp: generic number of legs, hash-map memo, explicit
// "segment" bookkeeping. A coupled state is (centre status, multiset of attached legs).
//   centre status: 0 = no marked edge (N), 1 = has an in-arc only (I), 2 = has an out-arc only (O)
//   leg = (r, f): r >= 1 unmarked edges from the centre outwards; f = 0 free far end,
//         1 = far end forces the last edge to point toward the centre, 2 = away from the centre.
// Detached runs are evaluated by the closed forms of Theorem 4.1.
// Usage: ./spiderk L1 L2 ... Lk   (ORIGINAL leg lengths, i.e. edges including the leaf edge)
#include <bits/stdc++.h>
using namespace std;
typedef vector<pair<int,int>> Legs;

static int runValue(int k, int a, int b) {           // a,b in {0 free, 1 toward, 2 away}
    if (k <= 0) return 0;
    if (a == 0 && b == 0) return k % 2;               // A_k
    if (a == 0 || b == 0) return k;                   // B_k
    if (a == b) return k % 2;                         // C_k
    return (k % 2 == 0) ? 1 : 0;                      // D_k (k>=2 even -> 1; k=1 -> 0)
}

struct Key {
    int status; Legs legs;
    bool operator==(const Key& o) const { return status == o.status && legs == o.legs; }
};
struct KH { size_t operator()(const Key& k) const {
    size_t h = k.status * 1000003u;
    for (auto& p : k.legs) h = h * 1315423911u + p.first * 7 + p.second;
    return h; } };
unordered_map<Key,int,KH> memo;

int value(int status, Legs legs);

// Value of a state that may need normalisation (centre free / at most one leg left).
int settle(int status, Legs legs) {
    if (status == 3) {                       // centre free: everything detaches
        int x = 0;
        for (auto& l : legs) x ^= runValue(l.first, 0, l.second);
        return x;
    }
    if (legs.empty()) return 0;
    if (legs.size() == 1 && status != 0) {
        // the last centre edge is forced: status I -> must point away (2); O -> toward (1)
        int nearForce = (status == 1) ? 2 : 1;
        return runValue(legs[0].first, nearForce, legs[0].second);
    }
    return value(status, legs);
}

int value(int status, Legs legs) {
    sort(legs.begin(), legs.end());
    Key key{status, legs};
    auto it = memo.find(key);
    if (it != memo.end()) return it->second;
    set<int> opts;
    int deg = legs.size();
    for (int i = 0; i < deg; i++) {
        int r = legs[i].first, f = legs[i].second;
        for (int j = 1; j <= r; j++) {
            for (int dir = 1; dir <= 2; dir++) {     // 1 = toward centre, 2 = away
                if (j == r && f != 0 && dir != f) continue;      // agree with far constraint
                if (j == 1 && deg == 1) {                      // last centre edge
                    if (!((status == 1 && dir == 2) || (status == 2 && dir == 1))) continue;
                }
                int detached = runValue(r - j, dir, f);
                Legs nl = legs;
                int ns = status;
                if (j >= 2) {
                    nl[i] = make_pair(j - 1, dir);
                } else {
                    nl.erase(nl.begin() + i);
                    bool in = (dir == 1);
                    if (status == 0) ns = in ? 1 : 2;
                    else if (status == 1) ns = in ? 1 : 3;
                    else ns = in ? 3 : 2;
                }
                opts.insert(detached ^ settle(ns, nl));
            }
        }
    }
    int g = 0;
    while (opts.count(g)) g++;
    memo[key] = g;
    return g;
}

int main(int argc, char** argv) {
    vector<int> L;
    for (int i = 1; i < argc; i++) L.push_back(atoi(argv[i]));
    // a leg of original length 1 makes the centre adjacent to a leaf, i.e. free
    bool centreFree = false;
    Legs legs;
    int m = 0;
    for (int l : L) {
        if (l == 1) centreFree = true;
        else legs.push_back(make_pair(l - 1, 0));
        m += l - 1;
    }
    int g = settle(centreFree ? 3 : 0, legs);
    printf("legs");
    for (int l : L) printf(" %d", l);
    printf(" markable=%d grundy=%d states=%zu\n", m, g, memo.size());
    return 0;
}
