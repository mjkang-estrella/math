// hsolve: fast single-tree solver for H(a1,a2|l|b1,b2).  Independent re-implementation of htree.cpp
// with compact per-tree leg codes, iterative bottom-up order and precomputed exit/bridge tables.
// Usage: ./hsolve a1 a2 l b1 b2 [a1 a2 l b1 b2 ...]  (several trees, each solved from scratch)
#include <bits/stdc++.h>
using namespace std;
typedef uint16_t u16;
static inline int runv(int k,int a,int b){ if(k<=0) return 0; if(a==0&&b==0) return k&1; if(a==0||b==0) return k; if(a==b) return k&1; return (k>=2&&!(k&1))?1:0;}
static inline int flipf(int f){return f==0?0:3-f;}
enum {SN=0,SI=1,SO=2,SF=3};
static inline int stepS(int s,int d){ if(s==SN) return d==1?SI:SO; if(s==SI) return d==1?SI:SF; if(s==SO) return d==2?SO:SF; return SF; }
// ---------- general 3-leg spider tables, full codes r*3+f, r<=M
int M, CC; vector<u16> NT, IT; vector<char> NK, IK;
static inline int cd(int r,int f){return r*3+f;}
static inline int fl(int c){return (c/3)*3+flipf(c%3);}
static uint32_t stA[1<<14]; static uint32_t stC=0;
int Ifun(int a,int b){ if(a>b) swap(a,b); size_t k=(size_t)a*CC+b; if(IK[k]) return IT[k];
  vector<int> o; int L[2]={a,b};
  for(int i=0;i<2;i++){int r=L[i]/3,f=L[i]%3,ro=L[1-i]/3,fo=L[1-i]%3;
    for(int j=1;j<=r;j++)for(int d=1;d<=2;d++){ if(j==r&&f&&d!=f) continue; int det=runv(r-j,d,f);
      if(j>=2) o.push_back(det^Ifun(cd(j-1,d),L[1-i])); else o.push_back(det^(d==1?runv(ro,2,fo):runv(ro,0,fo))); }}
  stC++; for(int x:o) stA[x]=stC; int g=0; while(stA[g]==stC) g++; IK[k]=1; IT[k]=g; return g; }
int Ofun(int a,int b){return Ifun(fl(a),fl(b));}
int Nfun(int a,int b,int c){ int v[3]={a,b,c}; sort(v,v+3); size_t k=((size_t)v[0]*CC+v[1])*CC+v[2]; if(NK[k]) return NT[k];
  vector<int> o;
  for(int i=0;i<3;i++){int r=v[i]/3,f=v[i]%3,o1=v[(i+1)%3],o2=v[(i+2)%3];
    for(int j=1;j<=r;j++)for(int d=1;d<=2;d++){ if(j==r&&f&&d!=f) continue; int det=runv(r-j,d,f);
      if(j>=2) o.push_back(det^Nfun(cd(j-1,d),o1,o2)); else o.push_back(det^(d==1?Ifun(o1,o2):Ofun(o1,o2))); }}
  stC++; for(int x:o) stA[x]=stC; int g=0; while(stA[g]==stC) g++; NK[k]=1; NT[k]=g; return g; }
int Gam(int s,const int* lg,int n){ if(n==0) return 0;
  if(s==SF){int x=0; for(int i=0;i<n;i++) x^=runv(lg[i]/3,0,lg[i]%3); return x;}
  if(s==SI||s==SO){ if(n==1) return runv(lg[0]/3, s==SI?2:1, lg[0]%3); if(n==2) return s==SI?Ifun(lg[0],lg[1]):Ofun(lg[0],lg[1]); abort();}
  if(n==3) return Nfun(lg[0],lg[1],lg[2]); abort(); }
// ---------- one side of the H with FULL leg codes; leg t has r <= Amax[t]; if sym, the two legs are
// interchangeable (Amax equal) and n-states store unordered pairs (i1<=i2).
int ELL;
struct SideSt { int s; int n; int leg[2]; };
struct Side {
  int Am[2], NCt[2], NS, NN; bool sym;
  vector<SideSt> st; vector<int> order;
  vector<vector<pair<int,int>>> inner, exits;
  vector<array<int,3>> brOther; vector<vector<array<int,2>>> bv;
  static int ci(int r,int f){ return 3*(r-1)+f; }
  static int codeOf(int i){ return cd(i/3+1,i%3); }
  int nIdx(int i1,int i2){ if(sym){ if(i1>i2) swap(i1,i2); return i2*(i2+1)/2+i1; } return i1*NCt[1]+i2; }
  // io-states: leg kept is identified by its code only when sym; otherwise by (t, code)
  int ioIdx(int s,int t,int i){ int base=NN + (s==SO? (sym?NCt[0]:NCt[0]+NCt[1]) : 0); if(sym) return base+i; return base + (t==1?NCt[0]:0) + i; }
  void build(int A1,int A2,bool sy){ sym=sy; Am[0]=A1; Am[1]=A2; NCt[0]=3*A1; NCt[1]=3*A2;
    NN = sym ? NCt[0]*(NCt[0]+1)/2 : NCt[0]*NCt[1];
    NS = NN + 2*(sym?NCt[0]:NCt[0]+NCt[1]); st.assign(NS,SideSt{});
    vector<int> legt0(NS,-1);
    for(int i1=0;i1<NCt[0];i1++)for(int i2=0;i2<NCt[1];i2++){ if(sym&&i1>i2) continue; SideSt x; x.s=SN; x.n=2; x.leg[0]=codeOf(i1); x.leg[1]=codeOf(i2); st[nIdx(i1,i2)]=x; }
    vector<int> keptT(NS,0);
    for(int s=SI;s<=SO;s++) for(int t=0;t<(sym?1:2);t++) for(int i=0;i<NCt[t];i++){ SideSt x; x.s=s; x.n=1; x.leg[0]=codeOf(i); int I=ioIdx(s,t,i); st[I]=x; keptT[I]=t; }
    inner.assign(NS,{}); exits.assign(NS,{}); brOther.resize(NS); bv.assign(NS, vector<array<int,2>>(ELL));
    for(int X=0;X<NS;X++){ SideSt& x=st[X];
      for(int t=0;t<x.n;t++){ int r=x.leg[t]/3,f=x.leg[t]%3;
        for(int j=1;j<=r;j++)for(int d=1;d<=2;d++){ if(j==r&&f&&d!=f) continue; int det=runv(r-j,d,f);
          if(j>=2){ int ni=ci(j-1,d); int T;
            if(x.s==SN){ int o=ci(x.leg[1-t]/3,x.leg[1-t]%3); T= t==0? nIdx(ni,o):nIdx(o,ni);} else T=ioIdx(x.s,keptT[X],ni);
            inner[X].push_back({T,det}); }
          else { int s2=stepS(x.s,d);
            if(s2==SF){ int v=det; for(int u=0;u<x.n;u++) if(u!=t) v^=runv(x.leg[u]/3,0,x.leg[u]%3); exits[X].push_back({0,v}); }
            else if(x.s==SN){ int ot=1-t; int T=ioIdx(s2,ot,ci(x.leg[ot]/3,x.leg[ot]%3)); inner[X].push_back({T,det}); }
            else { exits[X].push_back({s2==SI?1:2, det}); } } } }
      int lg[3]; for(int i=0;i<x.n;i++) lg[i]=x.leg[i];
      for(int f=0;f<3;f++){ lg[x.n]=cd(ELL,f); brOther[X][f]=Gam(x.s,lg,x.n+1); }
      for(int k=0;k<ELL;k++) for(int d=1;d<=2;d++){ if(k>=1){ lg[x.n]=cd(k,d); bv[X][k][d-1]=Gam(x.s,lg,x.n+1);} else bv[X][k][d-1]=Gam(stepS(x.s,d),lg,x.n); }
    }
    vector<pair<pair<int,int>,int>> key; for(int X=0;X<NS;X++){ SideSt& x=st[X]; int g= x.s==SN?1:0; int sr=0; for(int i=0;i<x.n;i++) sr+=x.leg[i]/3; key.push_back({{g,sr},X}); }
    sort(key.begin(),key.end()); order.clear(); for(auto&k:key) order.push_back(k.second);
  }
};
int main(int argc,char**argv){
  // ./hbatch2 l A1 A2 B thr [minm]  : all H(a1,a2|l|b1,b2), a1<=A1, a2<=A2, b1<=b2<=B
  int l=atoi(argv[1]),A1=atoi(argv[2]),A2=atoi(argv[3]),B=atoi(argv[4]),thr=atoi(argv[5]);
  auto t0=chrono::steady_clock::now();
  ELL=l; M=max({A1,A2,B,l})+1; CC=3*(M+1);
  NT.assign((size_t)CC*CC*CC,0); NK.assign((size_t)CC*CC*CC,0); IT.assign((size_t)CC*CC,0); IK.assign((size_t)CC*CC,0);
  Side U,V; U.build(A1,A2,false); V.build(B,B,true);
  size_t NU=U.NS, NV=V.NS; fprintf(stderr,"NU=%zu NV=%zu states=%.3g MB=%.0f\n",NU,NV,(double)NU*NV,(double)NU*NV*4/1e6);
  vector<u16> H(NU*NV), HTr(NU*NV);
  for(int X:U.order) for(int Y:V.order){
    stC++;
    for(auto& m:U.inner[X]) stA[m.second^HTr[(size_t)Y*NU+m.first]]=stC;
    for(auto& m:U.exits[X]) stA[m.second^V.brOther[Y][m.first]]=stC;
    for(auto& m:V.inner[Y]) stA[m.second^H[(size_t)X*NV+m.first]]=stC;
    for(auto& m:V.exits[Y]) stA[m.second^U.brOther[X][m.first]]=stC;
    for(int j=1;j<=l;j++){ stA[U.bv[X][j-1][1]^V.bv[Y][l-j][0]]=stC; stA[U.bv[X][j-1][0]^V.bv[Y][l-j][1]]=stC; }
    int g=0; while(stA[g]==stC) g++;
    H[(size_t)X*NV+Y]=g; HTr[(size_t)Y*NU+X]=g;
  }
  int best=-1;
  for(int a1=1;a1<=A1;a1++)for(int a2=1;a2<=A2;a2++)for(int b2=1;b2<=B;b2++)for(int b1=1;b1<=b2;b1++){
    int X=U.nIdx(Side::ci(a1,0),Side::ci(a2,0)), Y=V.nIdx(Side::ci(b1,0),Side::ci(b2,0));
    int g=H[(size_t)X*NV+Y]; if(g>best) best=g; if(g>=thr) printf("%d %d %d %d %d %d\n",a1,a2,l,b1,b2,g); }
  fprintf(stderr,"l=%d best=%d time=%.1f\n",l,best,chrono::duration<double>(chrono::steady_clock::now()-t0).count());
}
