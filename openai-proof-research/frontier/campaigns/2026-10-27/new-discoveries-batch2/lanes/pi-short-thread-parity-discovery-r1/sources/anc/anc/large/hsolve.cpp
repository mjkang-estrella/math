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
// ---------- one side of the H
int ELL;
struct SideSt { int s; int n; int leg[2]; int legid[2]; };
struct Side {
  int p[2], nn[2], NS;
  vector<SideSt> st; vector<int> order;
  vector<vector<pair<int,int>>> inner;   // (target state, det)
  vector<vector<pair<int,int>>> exits;   // (kind 0=F,1=T,2=A for the OTHER side's bridge leg, value)
  vector<array<int,3>> brOther;          // Gamma(s; legs + (ELL,f)) : used when the OTHER side exits
  vector<vector<array<int,2>>> bv;       // bv[X][k][dir-1], k=0..ELL-1
  int code(int t,int i){ return i<2*(p[t]-1) ? cd(i/2+1, i%2+1) : cd(p[t],0); }
  int nIdx(int i1,int i2){ return i1*nn[1]+i2; }
  int ioIdx(int s,int t,int i){ int b=nn[0]*nn[1]; if(s==SO) b+=nn[0]+nn[1]; if(t==1) b+=nn[0]; return b+i; }
  int legIndex(int t,int r,int f){ return f==0 ? 2*(p[t]-1) : 2*(r-1)+(f-1); }
  void build(int a,int b){ p[0]=a;p[1]=b; nn[0]=2*a-1; nn[1]=2*b-1; NS=nn[0]*nn[1]+2*(nn[0]+nn[1]); st.resize(NS);
    for(int i1=0;i1<nn[0];i1++)for(int i2=0;i2<nn[1];i2++){ SideSt x; x.s=SN; x.n=2; x.leg[0]=code(0,i1); x.leg[1]=code(1,i2); x.legid[0]=0; x.legid[1]=1; st[nIdx(i1,i2)]=x; }
    for(int s=SI;s<=SO;s++) for(int t=0;t<2;t++) for(int i=0;i<nn[t];i++){ SideSt x; x.s=s; x.n=1; x.leg[0]=code(t,i); x.legid[0]=t; st[ioIdx(s,t,i)]=x; }
    inner.assign(NS,{}); exits.assign(NS,{}); brOther.resize(NS); bv.assign(NS, vector<array<int,2>>(ELL));
    for(int X=0;X<NS;X++){ SideSt& x=st[X];
      for(int t=0;t<x.n;t++){ int r=x.leg[t]/3,f=x.leg[t]%3, id=x.legid[t];
        for(int j=1;j<=r;j++)for(int d=1;d<=2;d++){ if(j==r&&f&&d!=f) continue; int det=runv(r-j,d,f);
          if(j>=2){ int ni=legIndex(id,j-1,d); int T;
            if(x.s==SN){ int i1= id==0? ni : legIndex(0,x.leg[0]/3,x.leg[0]%3); int i2= id==1? ni : legIndex(1,x.leg[1]/3,x.leg[1]%3); T=nIdx(i1,i2);} else T=ioIdx(x.s,id,ni);
            inner[X].push_back({T,det}); }
          else { int s2=stepS(x.s,d);
            if(s2==SF){ int v=det; for(int u=0;u<x.n;u++) if(u!=t) v^=runv(x.leg[u]/3,0,x.leg[u]%3); exits[X].push_back({0,v}); }
            else if(x.s==SN){ int ot=1-t; int oid=x.legid[ot]; int T=ioIdx(s2,oid,legIndex(oid,x.leg[ot]/3,x.leg[ot]%3)); inner[X].push_back({T,det}); }
            else { exits[X].push_back({s2==SI?1:2, det}); } } } }
      int lg[3]; for(int i=0;i<x.n;i++) lg[i]=x.leg[i];
      for(int f=0;f<3;f++){ lg[x.n]=cd(ELL,f); brOther[X][f]=Gam(x.s,lg,x.n+1); }
      for(int k=0;k<ELL;k++) for(int d=1;d<=2;d++){ if(k>=1){ lg[x.n]=cd(k,d); bv[X][k][d-1]=Gam(x.s,lg,x.n+1);} else bv[X][k][d-1]=Gam(stepS(x.s,d),lg,x.n); }
    }
    vector<pair<pair<int,int>,int>> key; for(int X=0;X<NS;X++){ SideSt& x=st[X]; int g= x.s==SN?1:0; int sr=0; for(int i=0;i<x.n;i++) sr+=x.leg[i]/3; key.push_back({{g,sr},X}); }
    sort(key.begin(),key.end()); order.clear(); for(auto&k:key) order.push_back(k.second);
  }
};
int solveH(int a1,int a2,int l,int b1,int b2, double* secs){
  auto t0=chrono::steady_clock::now();
  ELL=l; M=max({a1,a2,b1,b2,l})+1; CC=3*(M+1);
  NT.assign((size_t)CC*CC*CC,0); NK.assign((size_t)CC*CC*CC,0); IT.assign((size_t)CC*CC,0); IK.assign((size_t)CC*CC,0);
  Side U,V; U.build(a1,a2); V.build(b1,b2);
  size_t NU=U.NS, NV=V.NS; vector<u16> H(NU*NV), HTr(NU*NV);
  for(int X:U.order) for(int Y:V.order){
    stC++;
    for(auto& m:U.inner[X]) stA[m.second^HTr[(size_t)Y*NU+m.first]]=stC;
    for(auto& m:U.exits[X]) stA[m.second^V.brOther[Y][m.first]]=stC;
    for(auto& m:V.inner[Y]) stA[m.second^H[(size_t)X*NV+m.first]]=stC;
    for(auto& m:V.exits[Y]) stA[m.second^U.brOther[X][m.first]]=stC;
    for(int j=1;j<=l;j++){ // bridge edge j from u; stub lengths j-1 (u side), l-j (v side)
      stA[U.bv[X][j-1][1]^V.bv[Y][l-j][0]]=stC;   // toward v: OUT for u (2), IN for v (1)
      stA[U.bv[X][j-1][0]^V.bv[Y][l-j][1]]=stC; } // toward u
    int g=0; while(stA[g]==stC) g++;
    H[(size_t)X*NV+Y]=g; HTr[(size_t)Y*NU+X]=g;
  }
  int X0=U.nIdx(2*(a1-1),2*(a2-1)), Y0=V.nIdx(2*(b1-1),2*(b2-1));
  if(secs) *secs=chrono::duration<double>(chrono::steady_clock::now()-t0).count();
  return H[(size_t)X0*NV+Y0];
}
int main(int argc,char**argv){
  for(int i=1;i+4<argc;i+=5){ int a1=atoi(argv[i]),a2=atoi(argv[i+1]),l=atoi(argv[i+2]),b1=atoi(argv[i+3]),b2=atoi(argv[i+4]); double s;
    int g=solveH(a1,a2,l,b1,b2,&s); printf("H %d %d %d %d %d m=%d g=%d time=%.2f\n",a1,a2,l,b1,b2,a1+a2+l+b1+b2,g,s); fflush(stdout);}
}
