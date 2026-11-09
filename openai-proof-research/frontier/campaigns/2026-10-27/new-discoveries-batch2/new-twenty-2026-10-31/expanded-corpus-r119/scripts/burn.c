// 361189 search: deficient n-path forests of order m^2 with all parts >= L (Tan-Teh, arXiv:2312.10914).
// A forest (l_1..l_n), sum m^2, is well-burnable iff {1,3,...,2m-1} partitions into n blocks with sums l_i.
// Induction: if T in D(m) has largest part l > 2m-2+L, its reduction (l -> l-(2m-1)) is in D(m-1).
// So D(m) is contained in Ext(D(m-1)) U Balanced(m), Balanced(m) = all parts in [L, 2m-2+L].
// Each candidate is decided exactly by DFS with exact-key memo of failed states.
// usage: burn n L mmax [print_limit]
#include "libc.h"
#define MAXN 12
static int n, L;
typedef struct { short c[MAXN]; } F;
static int cmpF(const void*a,const void*b){const short*x=((const F*)a)->c,*y=((const F*)b)->c;for(int i=0;i<n;i++){if(x[i]!=y[i])return x[i]<y[i]?-1:1;}return 0;}
static void sortA(short*c){for(int i=1;i<n;i++){short v=c[i];int j=i-1;while(j>=0&&c[j]>v){c[j+1]=c[j];j--;}c[j+1]=v;}}
// ---------- exact decision ----------
#define HB 21
#define HS (1u<<HB)
static uint64_t hk0[HS],hk1[HS]; static uint32_t hg[HS]; static uint32_t gen=0; static long hcount;
static long nodes;
static int tmin(int c,int k){ // least t>=1, t==c mod 2, c <= k^2-(k-t)^2 ; returns k+1 if none
  for(int t=(c&1)?1:2;t<=k;t+=2) if(c<=k*k-(k-t)*(k-t)) return t; return k+1;}
static int tmax(int c,int k){ int t=0; while((t+1)*(t+1)<=c && t+1<=k) t++; if((t&1)!=(c&1)) t--; return t;}
static int memo_has(uint64_t a,uint64_t b,int ins){
  uint64_t h=(a*0x9E3779B97F4A7C15ULL)^(b*0xC2B2AE3D27D4EB4FULL); uint32_t i=(uint32_t)(h>>(64-HB));
  while(hg[i]==gen){ if(hk0[i]==a&&hk1[i]==b) return 1; i=(i+1)&(HS-1);}
  if(ins && hcount < (long)(HS*0.7)){hg[i]=gen;hk0[i]=a;hk1[i]=b;hcount++;}
  return 0;}
static int dfs(int k, short*c){ // c sorted descending, sum = k^2, zeros allowed
  nodes++;
  if(k==0) return 1;
  int lo=0,hi=0;
  for(int i=0;i<n;i++) if(c[i]>0){int a=tmin(c[i],k),b=tmax(c[i],k); if(a>b) return 0; lo+=a; hi+=b;}
  if(lo>k||hi<k) return 0;
  uint64_t a=(uint64_t)k,b=0; for(int i=0;i<n;i++){ if(i<4) a=(a<<12)|(uint64_t)c[i]; else b=(b<<12)|(uint64_t)c[i]; }
  if(n<=4) b=0;
  if(memo_has(a,b,0)) return 0;
  int x=2*k-1; short d[MAXN];
  // try exact fit first
  for(int i=0;i<n;i++) if(c[i]==x){ memcpy(d,c,sizeof(short)*n); d[i]=0; // re-sort descending
      for(int j=i;j<n-1;j++){short t=d[j];d[j]=d[j+1];d[j+1]=t;}
      if(dfs(k-1,d)) return 1; break; }
  for(int i=0;i<n;i++){ if(c[i]<x+1) break; if(i>0&&c[i]==c[i-1]) continue; if(c[i]==x) continue;
      memcpy(d,c,sizeof(short)*n); d[i]-=x; int j=i; while(j<n-1&&d[j]<d[j+1]){short t=d[j];d[j]=d[j+1];d[j+1]=t;j++;}
      if(dfs(k-1,d)) return 1; }
  memo_has(a,b,1); return 0;}
static int burnable(int m,const short*asc){ short c[MAXN]; for(int i=0;i<n;i++) c[i]=asc[n-1-i]; gen++; hcount=0; if(gen==0){memset(hg,0,sizeof hg);gen=1;} return dfs(m,c);}
static int Bm(int m,int l){ for(int t=(l&1)?1:2;;t+=2) if(l<=2*m*t-t*t) return t; }
// ---------- candidate lists ----------
static F*cand; static long nc, capc;
static void push(const short*c){ if(nc==capc){capc=capc?capc*2:1024; F*nw=malloc(sizeof(F)*capc); if(nc) memcpy(nw,cand,sizeof(F)*nc); free(cand); cand=nw;} memset(&cand[nc],0,sizeof(F)); memcpy(cand[nc].c,c,sizeof(short)*n); nc++; }
static short cur[MAXN];
static void bal(int i,int rem,int lo,int hi){ // parts nondecreasing in [lo,hi], n-i parts left summing to rem
  int left=n-i; if(left==0){ if(rem==0) push(cur); return; }
  if((long)lo*left>rem || (long)hi*left<rem) return;
  for(int v=lo; v<=hi; v++){ if((long)v*left>rem) break; if((long)hi*(left-1) < rem-v) continue; cur[i]=v; bal(i+1,rem-v,v,hi);} }
int main(int argc,char**argv){
  n=atoi(argv[1]); L=atoi(argv[2]); int mmax=atoi(argv[3]); int plim=argc>4?atoi(argv[4]):50;
  F*D=0; long nd=0; int m=1; while(m*m<n*L) m++;
  long totdef=0,totnonib=0,totcand=0;
  for(;m<=mmax;m++){
    nc=0; int U=2*m-2+L;
    for(long t=0;t<nd;t++) for(int i=0;i<n;i++){ if(i>0&&D[t].c[i]==D[t].c[i-1]) continue; short c[MAXN]; memcpy(c,D[t].c,sizeof(short)*n); c[i]+=2*m-1; sortA(c); if(c[n-1]>U) push(c);}
    long next=nc;
    if((long)n*U>=(long)m*m) bal(0,m*m,L,U);
    long nbal=nc-next;
    qsort(cand,nc,sizeof(F),cmpF); long u=0; for(long t=0;t<nc;t++) if(u==0||cmpF(&cand[t],&cand[u-1])) cand[u++]=cand[t]; nc=u;
    F*ND=malloc(sizeof(F)*(nc?nc:1)); long nnd=0, nib=0, nonib=0; nodes=0;
    for(long t=0;t<nc;t++){ if(!burnable(m,cand[t].c)){ ND[nnd++]=cand[t]; int s=0; for(int i=0;i<n;i++) s+=Bm(m,cand[t].c[i]); if(s>m) nib++; else { nonib++; if(totnonib+nonib<=plim){ printf("NONIB m=%d sumB=%d (",m,s); for(int i=0;i<n;i++) printf("%d%s",cand[t].c[i],i<n-1?",":")\n"); } } } }
    totcand+=nc; totdef+=nnd; totnonib+=nonib;
    printf("n=%d L=%d m=%d ext=%ld balanced=%ld candidates=%ld deficient=%ld (IB=%ld nonIB=%ld) dfs_nodes=%ld\n",n,L,m,next,nbal,nc,nnd,nib,nonib,nodes); fflush(stdout);
    free(D); D=ND; nd=nnd;
    if(nd==0 && (long)n*(2*(m+1)-2+L) < (long)(m+1)*(m+1)){ printf("CLOSED: D(m)=empty and Balanced(m')=empty for all m'>%d, so no deficient forest for any larger m\n",m); break; }
  }
  printf("TOTAL candidates=%ld deficient=%ld nonIB=%ld last_m=%d\n",totcand,totdef,totnonib,m);
  return 0; }
