// htree: Grundy values of H-trees H(a1,a2|l|b1,b2) (two branch vertices u,v of degree 3 joined by a
// bridge of l markable edges; legs a1,a2 at u and b1,b2 at v, each ending in a pendant edge).
// Own implementation based on Lemma 3.2/Prop 3.6 (status-labelled forests), Thm 4.3 (runs), and the
// 3-leg spider recursion (Prop 6.1) for components with one branch vertex.
// Usage: ./htree single a1 a2 l b1 b2      |   ./htree batch l A B   (all a1<=a2<=A, b1<=b2<=B)
#include <bits/stdc++.h>
using namespace std;
typedef uint16_t u16;
static inline int runv(int k,int a,int b){ if(k<=0) return 0; if(a==0&&b==0) return k&1; if(a==0||b==0) return k; if(a==b) return k&1; return (k>=2&&!(k&1))?1:0;}
static inline int flipf(int f){return f==0?0:3-f;}
enum {SN=0,SI=1,SO=2,SF=3};
static inline int stepS(int s,int d){ // d=1: arc into centre (T), d=2: arc out of centre (A)
  if(s==SN) return d==1?SI:SO; if(s==SI) return d==1?SI:SF; if(s==SO) return d==2?SO:SF; return SF; }
int M; int CC; // codes: r*3+f, r in [0,M]
vector<u16> NT, IT; vector<char> NK, IK;
static inline int cd(int r,int f){return r*3+f;}
int Ifun(int a,int b); int Nfun(int a,int b,int c);
int mexv(vector<int>&v){ static vector<char> s; s.assign(v.size()+2,0); for(int x:v) if(x<(int)s.size()) s[x]=1; int g=0; while(s[g]) g++; return g; }
int Ifun(int a,int b){ if(a>b) swap(a,b); size_t k=(size_t)a*CC+b; if(IK[k]) return IT[k];
  vector<int> o; int L[2]={a,b};
  for(int i=0;i<2;i++){int r=L[i]/3,f=L[i]%3,ro=L[1-i]/3,fo=L[1-i]%3;
    for(int j=1;j<=r;j++)for(int d=1;d<=2;d++){ if(j==r&&f&&d!=f) continue; int det=runv(r-j,d,f);
      if(j>=2) o.push_back(det^Ifun(cd(j-1,d),L[1-i])); else o.push_back(det^(d==1?runv(ro,2,fo):runv(ro,0,fo))); }}
  int g=mexv(o); IK[k]=1; IT[k]=g; return g; }
static inline int fl(int c){return (c/3)*3+flipf(c%3);}
int Ofun(int a,int b){return Ifun(fl(a),fl(b));}
int Nfun(int a,int b,int c){ int v[3]={a,b,c}; sort(v,v+3); size_t k=((size_t)v[0]*CC+v[1])*CC+v[2]; if(NK[k]) return NT[k];
  vector<int> o;
  for(int i=0;i<3;i++){int r=v[i]/3,f=v[i]%3,o1=v[(i+1)%3],o2=v[(i+2)%3];
    for(int j=1;j<=r;j++)for(int d=1;d<=2;d++){ if(j==r&&f&&d!=f) continue; int det=runv(r-j,d,f);
      if(j>=2) o.push_back(det^Nfun(cd(j-1,d),o1,o2)); else o.push_back(det^(d==1?Ifun(o1,o2):Ofun(o1,o2))); }}
  int g=mexv(o); NK[k]=1; NT[k]=g; return g; }
// value of a one-centre component: status s, legs (codes, r>=1)
int Gam(int s, vector<int> legs){
  if(legs.empty()) return 0;
  if(s==SF){int x=0; for(int c:legs) x^=runv(c/3,0,c%3); return x;}
  if(s==SI||s==SO){ if(legs.size()==1) return runv(legs[0]/3, s==SI?2:1, legs[0]%3);
     if(legs.size()==2) return s==SI?Ifun(legs[0],legs[1]):Ofun(legs[0],legs[1]);
     fprintf(stderr,"bad Gam\n"); exit(1);}
  if(legs.size()==3) return Nfun(legs[0],legs[1],legs[2]);
  fprintf(stderr,"bad Gam N %zu\n",legs.size()); exit(1);
}
// H-states. side state: s in {SN (2 legs), SI/SO (1 leg)}; encode: SN: 0 + P*NC+Q ; SI: NC*NC + P ; SO: NC*NC+NC+P
int A_, NCs; int ELL;
struct Side{int s; int L[2]; int n;};
static inline int encS(const Side& x){ if(x.s==SN){int p=x.L[0],q=x.L[1]; if(p>q) swap(p,q); return p*NCs+q;} return NCs*NCs+(x.s==SI?0:NCs)+x.L[0]; }
static inline Side decS(int e){ Side x; if(e<NCs*NCs){x.s=SN;x.n=2;x.L[0]=e/NCs;x.L[1]=e%NCs;} else {e-=NCs*NCs; x.s= e<NCs?SI:SO; x.n=1; x.L[0]=e%NCs;} return x; }
int NSide; vector<u16> HT; vector<char> HK;
int Hfun(int eu,int ev);
// value of the other side Y as a spider with bridge leg added
int sideWithBridge(const Side& Y,int bridgeCode){ vector<int> lg; for(int i=0;i<Y.n;i++) lg.push_back(Y.L[i]); lg.push_back(bridgeCode); return Gam(Y.s,lg);}
int Hfun(int eu,int ev){ size_t k=(size_t)eu*NSide+ev; if(HK[k]) return HT[k];
  Side S[2]={decS(eu),decS(ev)}; vector<int> o;
  for(int X=0;X<2;X++){ const Side& Sx=S[X]; const Side& Sy=S[1-X];
    for(int t=0;t<Sx.n;t++){ int r=Sx.L[t]/3,f=Sx.L[t]%3;
      for(int j=1;j<=r;j++)for(int d=1;d<=2;d++){ if(j==r&&f&&d!=f) continue; int det=runv(r-j,d,f);
        if(j>=2){ Side N2=Sx; N2.L[t]=cd(j-1,d); int e2=encS(N2); o.push_back(det^(X==0?Hfun(e2,ev):Hfun(eu,e2))); }
        else { int s2=stepS(Sx.s,d);
          if(s2==SF){ int x=det; for(int u=0;u<Sx.n;u++) if(u!=t) x^=runv(Sx.L[u]/3,0,Sx.L[u]%3);
            x^=sideWithBridge(Sy,cd(ELL,0)); o.push_back(x); }
          else if(Sx.s==SN){ Side N2; N2.s=s2; N2.n=1; N2.L[0]=Sx.L[1-t]; int e2=encS(N2); o.push_back(det^(X==0?Hfun(e2,ev):Hfun(eu,e2))); }
          else { // no legs left at X, X has status s2 in {SI,SO}, bridge edge at X forced: SI -> points away from X = toward Y (T for Y)
            o.push_back(det^sideWithBridge(Sy,cd(ELL, s2==SI?1:2))); }
        }}}
  }
  // bridge moves: edge j from u (1..ELL), dir +: toward v, -: toward u
  for(int j=1;j<=ELL;j++) for(int dir=0;dir<2;dir++){ // dir 0 = toward v
    int uval,vval;
    { const Side& U=S[0]; vector<int> lg; for(int i=0;i<U.n;i++) lg.push_back(U.L[i]);
      if(j>=2){ lg.push_back(cd(j-1, dir==0?2:1)); uval=Gam(U.s,lg);} else { int s2=stepS(U.s, dir==0?2:1); uval=Gam(s2,lg);} }
    { const Side& V=S[1]; vector<int> lg; for(int i=0;i<V.n;i++) lg.push_back(V.L[i]);
      if(j<=ELL-1){ lg.push_back(cd(ELL-j, dir==0?1:2)); vval=Gam(V.s,lg);} else { int s2=stepS(V.s, dir==0?1:2); vval=Gam(s2,lg);} }
    o.push_back(uval^vval);
  }
  int g=mexv(o); HK[k]=1; HT[k]=g; return g; }
void setup(int A,int B,int l){ ELL=l; A_=max(A,B); M=max(A_,l)+1; CC=3*(M+1); NT.assign((size_t)CC*CC*CC,0); NK.assign((size_t)CC*CC*CC,0); IT.assign((size_t)CC*CC,0); IK.assign((size_t)CC*CC,0);
  NCs=3*(A_+1); NSide=NCs*NCs+2*NCs; HT.assign((size_t)NSide*NSide,0); HK.assign((size_t)NSide*NSide,0); }
int Hroot(int a1,int a2,int b1,int b2){ Side U{SN,{cd(a1,0),cd(a2,0)},2}, V{SN,{cd(b1,0),cd(b2,0)},2}; return Hfun(encS(U),encS(V)); }
int main(int argc,char**argv){ string m=argv[1];
  if(m=="single"){int a1=atoi(argv[2]),a2=atoi(argv[3]),l=atoi(argv[4]),b1=atoi(argv[5]),b2=atoi(argv[6]); setup(max(a1,a2),max(b1,b2),l);
    printf("%d\n",Hroot(a1,a2,b1,b2)); return 0;}
  if(m=="batch"){int l=atoi(argv[2]),A=atoi(argv[3]),B=atoi(argv[4]); setup(A,B,l);
    for(int a2=1;a2<=A;a2++)for(int a1=1;a1<=a2;a1++)for(int b2=1;b2<=B;b2++)for(int b1=1;b1<=b2;b1++)
      printf("%d %d %d %d %d %d\n",a1,a2,l,b1,b2,Hroot(a1,a2,b1,b2)); return 0;}
}
