// Driver for arrows.h
// Input lines:
//   T n u1 v1 ... u_{n-1} v_{n-1}        original tree  -> prints "g m"
//   P n u1 v1 ...                        piece (leaves f, others n) -> prints "g |E|"
//   L n s_0 ... s_{n-1} k u1 v1 ... uk vk  labelled forest (s in 0..3 = n,i,o,f) -> prints "g k"
// Flags: -notwin  disables twin reduction.
#include "arrows.h"
int main(int argc, char** argv) {
    Solver S;
    for (int i = 1; i < argc; i++) { if (string(argv[i]) == "-notwin") S.twin = false; if (string(argv[i]) == "-non4") S.n4 = false; }
    string line;
    while (getline(cin, line)) {
        if (line.empty()) continue;
        istringstream in(line);
        string mode; in >> mode;
        int n; in >> n;
        if (mode == "T" || mode == "P") {
            vector<pair<int, int>> E(n - 1);
            for (auto& e : E) in >> e.first >> e.second;
            if (mode == "T") { int m; int g = S.grundyTree(n, E, &m); printf("%d %d\n", g, m); }
            else { int g = S.grundyPiece(n, E); printf("%d %d\n", g, (int)E.size()); }
        } else if (mode == "L") {
            uint8_t lab[MAXV];
            for (int i = 0; i < n; i++) { int s; in >> s; lab[i] = s; }
            int k; in >> k;
            vector<pair<int, int>> E(k);
            for (auto& e : E) in >> e.first >> e.second;
            int g = S.grundyForest(n, lab, E);
            printf("%d %d\n", g, k);
        }
        fflush(stdout);
    }
    fprintf(stderr, "nodes=%llu memo=%zu\n", (unsigned long long)S.nodes, S.memo.used);
}
