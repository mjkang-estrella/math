// cubek: Grundy values of ALL k-legged spiders (k=KL compile-time, 3..6) with legs <= M,
// via Prop 6.1 on sorted code multisets (colex index).  codes c=3(r-1)+f.
#include <bits/stdc++.h>
using namespace std;
typedef uint16_t u16;
#ifndef KL
#define KL 5
#endif
static inline int runv(int k,int a,int b){ if(k<=0) return 0; if(a==0&&b==0) return k&1; if(a==0||b==0) return k; if(a==b) return k&1; return (k>=2&&!(k&1))?1:0;}
static inline int flipf(int f){return f==0?0:3-f;}
int M,NC; vector<vector<uint64_t>> Bn;
static inline int rr(int c){return c/3+1;} static inline int ff(int c){return c%3;}
static inline int cc(int r,int f){return 3*(r-1)+f;}
static inline int flc(int c){return cc(rr(c),flipf(ff(c)));}
static inline uint64_t idxn(const int* c,int n){ uint64_t s=0; for(int i=0;i<n;i++) s+=Bn[i+1][c[i]+i]; return s; }
vector<u16> TAB[KL+1]; // TAB[n] for n legs: n==KL -> centre n ; n<KL -> centre i
static uint32_t stA[1<<15]; static uint32_t stC=0;
static inline int stepS(int s,int d){ if(s==0) return d; if(s==1) return d==1?1:3; if(s==2) return d==2?2:3; return 3; }
int cent(int s,const int* L,int n){ // centre status s in {1,2,3}, n legs (n<KL)
  if(n==0) return 0;
  if(s==3){ int x=0; for(int i=0;i<n;i++) x^=runv(rr(L[i]),0,ff(L[i])); return x; }
  int T[KL]; for(int i=0;i<n;i++) T[i]=(s==2)?flc(L[i]):L[i];
  if(n==1) return runv(rr(T[0]),2,ff(T[0]));
  sort(T,T+n); return TAB[n][idxn(T,n)];
}
int solveState(int s,const int* L,int n){ // s=0 (n==KL) or s=1 (I-state)
  stC++;
  for(int t=0;t<n;t++){ if(t>0&&L[t]==L[t-1]) continue; int r=rr(L[t]),f=ff(L[t]);
    int O[KL]; int no=0; for(int u=0;u<n;u++) if(u!=t) O[no++]=L[u];
    for(int j=1;j<=r;j++) for(int d=1;d<=2;d++){ if(j==r&&f&&d!=f) continue; int det=runv(r-j,d,f),v;
      if(j>=2){ int c[KL]; for(int u=0;u<n;u++) c[u]= u==t? cc(j-1,d):L[u]; sort(c,c+n); v=TAB[n][idxn(c,n)]; }
      else v=cent(stepS(s,d),O,no);
      stA[det^v]=stC; } }
  int g=0; while(stA[g]==stC) g++; return g;
}
void enumerate(int n, function<void(int*)> fn){ // colex order over multisets of size n from [0,NC)
  int c[KL]; for(int i=0;i<n;i++) c[i]=0;
  while(true){ fn(c); int i=0; while(i<n){ if(i+1<n && c[i]<c[i+1]){ c[i]++; for(int k=0;k<i;k++) c[k]=0; break;} else if(i==n-1){ if(c[i]+1<NC){ c[i]++; for(int k=0;k<i;k++) c[k]=0; break;} else return; } i++; } }
}
int main(int argc,char**argv){
  M=atoi(argv[1]); int thr=argc>2?atoi(argv[2]):1000; NC=3*M;
  Bn.assign(KL+2, vector<uint64_t>(NC+KL+4,0));
  for(int i=0;i<=KL+1;i++) for(int d=0;d<NC+KL+4;d++){ if(d<i) continue; unsigned __int128 x=1; for(int k=1;k<=i;k++) x=x*(d-k+1)/k; Bn[i][d]=(uint64_t)x; }
  for(int n=2;n<=KL;n++){ int top[KL]; for(int i=0;i<n;i++) top[i]=NC-1; size_t sz=idxn(top,n)+1; TAB[n].assign(sz,0);
    fprintf(stderr,"n=%d states %zu\n",n,sz);
    int s= n==KL?0:1;
    vector<int> Lmax(M+1,-1); vector<array<int,KL>> arg(M+1); vector<long long> hist(1<<15,0);
    enumerate(n,[&](int* c){ int g=solveState(s,c,n); TAB[n][idxn(c,n)]=g;
      if(n==KL){ bool allF=true; for(int i=0;i<n;i++) if(ff(c[i])) allF=false;
        if(allF){ int z=rr(c[n-1]); hist[g]++; if(g>Lmax[z]){Lmax[z]=g; for(int i=0;i<n;i++) arg[z][i]=rr(c[i]);}
          if(g>=thr){ printf("S"); for(int i=0;i<n;i++) printf(" %d",rr(c[i])); printf(" g=%d\n",g);} } } });
    if(n==KL){ int run=-1; for(int z=1;z<=M;z++){ run=max(run,Lmax[z]); printf("L=%d max=%d at S(",z,Lmax[z]); for(int i=0;i<n;i++) printf("%d%s",arg[z][i],i<n-1?",":")"); printf(" upto=%d\n",run);} 
      printf("hist:"); for(int g=0;g<(1<<15);g++) if(hist[g]) printf(" %d:%lld",g,hist[g]); printf("\n"); }
  }
}
