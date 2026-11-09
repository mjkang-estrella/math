// Independent spider solver (my own derivation from the raw rules, validated
// against the raw brute force).  State of the centre component: status s of the
// centre c in {n,i,o} (status "both in and out" splits the component) and the
// multiset of attached legs (h, far), h>=1 unmarked edges counted from c, far in
// {free, IN, OUT}.  Detached runs are solved by a separate DP over raw path moves.
//
// Modes:
//   ./spider val x1 x2 ... xk        -> Grundy value of S(x1..xk) (k<=4)
//   ./spider pos x1..xk ; s h1 f1 ... -> (unused)
//   ./spider sweep L                  -> all 3-leg spiders with legs<=L: per-g minimal-m spider etc.
//   ./spider family x y Z             -> values g(S(x,y,z)) for z=1..Z
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;

enum { FREE = 0, IN = 1, OUT = 2 };   // also run constraints: 0 none, 1 = L (towards c), 2 = R (away from c)
enum { SN = 0, SI = 1, SO = 2, SF = 3 };

int K;                       // max run length
vector<array<array<int,3>,3>> RUN;  // RUN[k][a][b]
void build_runs(int maxk) {
    K = maxk; RUN.assign(maxk + 1, {});
    for (int k = 0; k <= maxk; k++) for (int a = 0; a < 3; a++) for (int b = 0; b < 3; b++) {
        if (k == 0) { RUN[k][a][b] = 0; continue; }
        // options: orient e_j (1..k) in direction d in {1(L),2(R)}
        vector<char> seen(2 * k + 4, 0);
        for (int j = 1; j <= k; j++) for (int d = 1; d <= 2; d++) {
            if (j == 1 && a != 0 && a != d) continue;
            if (j == k && b != 0 && b != d) continue;
            int v = RUN[j - 1][a][d] ^ RUN[k - j][d][b];
            if (v < (int)seen.size()) seen[v] = 1;
        }
        int r = 0; while (r < (int)seen.size() && seen[r]) r++;
        RUN[k][a][b] = r;
    }
}
static inline int sstep(int s, int arc /*IN or OUT relative to c*/) {
    // centre gains an incoming (IN) or outgoing (OUT) arc
    if (s == SN) return arc == IN ? SI : SO;
    if (s == SI) return arc == IN ? SI : SF;
    if (s == SO) return arc == OUT ? SO : SF;
    return SF;
}
// leg code: h>=1, far in {0,1,2}: code = (h-1)*3 + far + 1
static inline int code(int h, int f) { return (h - 1) * 3 + f + 1; }
static inline int hof(int c) { return (c - 1) / 3 + 1; }
static inline int fof(int c) { return (c - 1) % 3; }

// ---------- storage: hash for generic, dense for 3-leg sweep
struct Hash {
    vector<u64> k; vector<int16_t> v; size_t mask, used = 0;
    Hash() { k.assign(1 << 22, ~0ULL); v.assign(1 << 22, 0); mask = (1 << 22) - 1; }
    static inline u64 h(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
    int get(u64 key) { size_t i = h(key) & mask; while (k[i] != ~0ULL) { if (k[i] == key) return v[i]; i = (i + 1) & mask; } return -1; }
    void put(u64 key, int val) {
        if ((used + 1) * 2 > k.size()) { vector<u64> ok; vector<int16_t> ov; ok.swap(k); ov.swap(v); k.assign(ok.size() * 2, ~0ULL); v.assign(ok.size() * 2, 0); mask = k.size() - 1; used = 0; for (size_t i = 0; i < ok.size(); i++) if (ok[i] != ~0ULL) put(ok[i], ov[i]); }
        size_t i = h(key) & mask; while (k[i] != ~0ULL) { if (k[i] == key) { v[i] = val; return; } i = (i + 1) & mask; }
        k[i] = key; v[i] = val; used++;
    }
};
Hash H;
bool dense = false; int DC = 0; vector<uint8_t> D;   // dense: value+1, 0 = unknown

int G(int s, vector<int> legs);  // legs: codes, any order

int Gsorted(int s, vector<int>& legs) {
    // legs sorted descending, all >=1
    int d = legs.size();
    if (d == 0) return 0;
    u64 key = 0; size_t di = 0;
    if (dense) {
        int c[3] = {0, 0, 0}; for (int i = 0; i < d; i++) c[i] = legs[i];
        di = (((size_t)s * DC + c[0]) * DC + c[1]) * DC + c[2];
        if (D[di]) return D[di] - 1;
    } else {
        key = s; for (int i = 0; i < d; i++) key = (key << 14) | legs[i]; key = (key << 3) | d;
        int r = H.get(key); if (r >= 0) return r;
    }
    static thread_local int dummy;
    vector<char> seen(1024, 0);
    for (int t = 0; t < d; t++) {
        if (t > 0 && legs[t] == legs[t - 1]) continue;  // identical legs give identical options
        int h = hof(legs[t]), far = fof(legs[t]);
        vector<int> rest; rest.reserve(d);
        for (int u = 0; u < d; u++) if (u != t) rest.push_back(legs[u]);
        for (int j = 1; j <= h; j++) for (int dl = IN; dl <= OUT; dl++) {
            if (j == h && far != FREE && dl != far) continue;
            if (j == 1 && d == 1) {   // centre has a single unmarked edge
                // OUT gives c an outgoing arc: legal iff c already has an incoming arc
                if (dl == OUT && s != SI) continue;
                if (dl == IN && s != SO) continue;
            }
            int det = RUN[h - j][dl][far];
            int att;
            if (j >= 2) {
                vector<int> nl = rest; nl.push_back(code(j - 1, dl));
                att = G(s, nl);
            } else {
                int s2 = sstep(s, dl);
                if (s2 == SF) { att = 0; for (int c : rest) att ^= RUN[hof(c)][FREE][fof(c)]; }
                else att = G(s2, rest);
            }
            int v = det ^ att;
            if (v >= (int)seen.size()) seen.resize(v + 1, 0);
            seen[v] = 1;
        }
    }
    int r = 0; while (r < (int)seen.size() && seen[r]) r++;
    if (dense) D[di] = r + 1; else H.put(key, r);
    return r;
}
int G(int s, vector<int> legs) { sort(legs.rbegin(), legs.rend()); return Gsorted(s, legs); }

int spider_value(const vector<int>& xs) {
    vector<int> legs; for (int x : xs) legs.push_back(code(x, FREE));
    return G(SN, legs);
}


// ======================================================================================
// hverify: second, independent implementation for two-centre trees (H-trees), written
// from scratch on top of the independent spider solver above (verify/spider.cpp, by another
// author, from the paper's text).  Runs come from the raw-move DP RUN[][][] (no closed forms).
// State: (su, U-legs, sv, V-legs), bridge of length ELLV between u and v (unchanged while intact).
// ======================================================================================
int ELLV;
Hash H2;
static int settle1(int s, vector<int> legs){
  if(s==SF){ int x=0; for(int c:legs) x^=RUN[hof(c)][FREE][fof(c)]; return x; }
  return G(s, legs);
}
int two(int su, vector<int> U, int sv, vector<int> V);
static int settle2(int su, vector<int> U, int sv, vector<int> V){
  if(su==SF){ int x=0; for(int c:U) x^=RUN[hof(c)][FREE][fof(c)]; V.push_back(code(ELLV,FREE)); return x^settle1(sv,V); }
  if(sv==SF){ int x=0; for(int c:V) x^=RUN[hof(c)][FREE][fof(c)]; U.push_back(code(ELLV,FREE)); return x^settle1(su,U); }
  if(U.empty()){ // u has only the bridge edge left; su in {SI,SO}: SI forces the bridge edge out of u = into v
    V.push_back(code(ELLV, su==SI?IN:OUT)); return settle1(sv,V); }
  if(V.empty()){ U.push_back(code(ELLV, sv==SI?IN:OUT)); return settle1(su,U); }
  return two(su,U,sv,V);
}
int two(int su, vector<int> U, int sv, vector<int> V){
  sort(U.begin(),U.end()); sort(V.begin(),V.end());
  u64 key=(u64)su; key=(key<<2)|sv; key=(key<<2)|U.size(); key=(key<<2)|V.size();
  for(int i=0;i<2;i++) key=(key<<14)|(i<(int)U.size()?U[i]:0);
  for(int i=0;i<2;i++) key=(key<<14)|(i<(int)V.size()?V[i]:0);
  int r=H2.get(key); if(r>=0) return r;
  vector<char> seen(2048,0);
  auto mark=[&](int v){ if(v>=(int)seen.size()) seen.resize(v+1,0); seen[v]=1; };
  for(int side=0;side<2;side++){
    vector<int>& L = side==0?U:V; int s = side==0?su:sv;
    for(size_t t=0;t<L.size();t++){
      int h=hof(L[t]), far=fof(L[t]);
      for(int j=1;j<=h;j++) for(int dl=IN;dl<=OUT;dl++){
        if(j==h && far!=FREE && dl!=far) continue;
        int det=RUN[h-j][dl][far];
        vector<int> NL=L; int ns=s;
        if(j>=2) NL[t]=code(j-1,dl); else { NL.erase(NL.begin()+t); ns=sstep(s,dl); }
        int v = side==0 ? settle2(ns,NL,sv,V) : settle2(su,U,ns,NL);
        mark(det^v);
      }
    }
  }
  for(int j=1;j<=ELLV;j++) for(int towardV=0;towardV<2;towardV++){
    int du = towardV?OUT:IN, dv = towardV?IN:OUT;
    int uv, vv;
    { vector<int> L=U; if(j>=2){ L.push_back(code(j-1,du)); uv=settle1(su,L);} else uv=settle1(sstep(su,du),L); }
    { vector<int> L=V; if(j<=ELLV-1){ L.push_back(code(ELLV-j,dv)); vv=settle1(sv,L);} else vv=settle1(sstep(sv,dv),L); }
    mark(uv^vv);
  }
  int g=0; while(g<(int)seen.size()&&seen[g]) g++;
  H2.put(key,g); return g;
}
int main(int argc,char**argv){
  for(int i=1;i+4<argc;i+=5){
    int a1=atoi(argv[i]),a2=atoi(argv[i+1]),l=atoi(argv[i+2]),b1=atoi(argv[i+3]),b2=atoi(argv[i+4]);
    ELLV=l; build_runs(max({a1,a2,b1,b2,l})+2); H=Hash(); H2=Hash();
    int g=two(SN,{code(a1,FREE),code(a2,FREE)},SN,{code(b1,FREE),code(b2,FREE)});
    printf("H %d %d %d %d %d m=%d g=%d states2=%zu states1=%zu\n",a1,a2,l,b1,b2,a1+a2+l+b1+b2,g,H2.used,H.used); fflush(stdout);
  }
}
