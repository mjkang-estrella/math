// 361189 chunked search (same mathematics as burn.c, resumable).
// usage: burn2 n L m prevfile outfile skip limit
//  prevfile: binary list of D(m-1) forests (n shorts each, ascending), or "-" for empty.
//  Processes: if skip==0, all extensions of D(m-1) whose new largest part exceeds U=2m-2+L;
//  then balanced candidates (parts in [L,U], sum m^2, lexicographic order) with index in [skip, skip+limit).
//  Appends deficient forests to outfile; prints one summary line incl. next index (or DONE).
#include "libc.h"
#define MAXN 12
static int n, L;
static void sortA(short*c){for(int i=1;i<n;i++){short v=c[i];int j=i-1;while(j>=0&&c[j]>v){c[j+1]=c[j];j--;}c[j+1]=v;}}
#define HB 21
#define HS (1u<<HB)
static uint64_t hk0[HS],hk1[HS]; static uint32_t hg[HS]; static uint32_t gen=0; static long hcount; static long nodes;
static int tmin(int c,int k){for(int t=(c&1)?1:2;t<=k;t+=2) if(c<=k*k-(k-t)*(k-t)) return t; return k+1;}
static int tmax(int c,int k){int t=0; while((t+1)*(t+1)<=c && t+1<=k) t++; if((t&1)!=(c&1)) t--; return t;}
static int memo_has(uint64_t a,uint64_t b,int ins){
  uint64_t h=(a*0x9E3779B97F4A7C15ULL)^(b*0xC2B2AE3D27D4EB4FULL); uint32_t i=(uint32_t)(h>>(64-HB));
  while(hg[i]==gen){ if(hk0[i]==a&&hk1[i]==b) return 1; i=(i+1)&(HS-1);}
  if(ins && hcount < (long)(HS*0.7)){hg[i]=gen;hk0[i]=a;hk1[i]=b;hcount++;}
  return 0;}
static int dfs(int k, short*c){
  nodes++; if(k==0) return 1;
  int lo=0,hi=0;
  for(int i=0;i<n;i++) if(c[i]>0){int a=tmin(c[i],k),b=tmax(c[i],k); if(a>b) return 0; lo+=a; hi+=b;}
  if(lo>k||hi<k) return 0;
  uint64_t a=(uint64_t)k,b=0; for(int i=0;i<n;i++){ if(i<4) a=(a<<12)|(uint64_t)c[i]; else b=(b<<12)|(uint64_t)c[i]; }
  if(memo_has(a,b,0)) return 0;
  int x=2*k-1; short d[MAXN];
  for(int i=0;i<n;i++) if(c[i]==x){ memcpy(d,c,sizeof(short)*n); d[i]=0; for(int j=i;j<n-1;j++){short t=d[j];d[j]=d[j+1];d[j+1]=t;} if(dfs(k-1,d)) return 1; break; }
  for(int i=0;i<n;i++){ if(c[i]<x+1) break; if(i>0&&c[i]==c[i-1]) continue;
      memcpy(d,c,sizeof(short)*n); d[i]-=x; int j=i; while(j<n-1&&d[j]<d[j+1]){short t=d[j];d[j]=d[j+1];d[j+1]=t;j++;}
      if(dfs(k-1,d)) return 1; }
  memo_has(a,b,1); return 0;}
static int burnable(int m,const short*asc){ short c[MAXN]; for(int i=0;i<n;i++) c[i]=asc[n-1-i]; gen++; hcount=0; if(gen==0){memset(hg,0,sizeof hg);gen=1;} return dfs(m,c);}
static int Bm(int m,int l){ for(int t=(l&1)?1:2;;t+=2) if(l<=2*m*t-t*t) return t; }
static int M; static FILE*out; static long ndef,nib,nonib,ntest;
static void test(const short*c){ ntest++; if(!burnable(M,c)){ ndef++; fwrite(c,sizeof(short),n,out); int s=0; for(int i=0;i<n;i++) s+=Bm(M,c[i]); if(s>M) nib++; else { nonib++; printf("NONIB m=%d sumB=%d (",M,s); for(int i=0;i<n;i++) printf("%d%s",c[i],i<n-1?",":")\n"); fflush(stdout);} } }
static short cur[MAXN]; static long idx, skip, lim;
static void bal(int i,int rem,int lo,int hi){
  if(idx>=skip+lim) return;
  int left=n-i; if(left==0){ if(rem==0){ if(idx>=skip) test(cur); idx++; } return; }
  if((long)lo*left>rem || (long)hi*left<rem) return;
  for(int v=lo; v<=hi; v++){ if((long)v*left>rem) break; if((long)hi*(left-1) < rem-v) continue; cur[i]=v; bal(i+1,rem-v,v,hi); if(idx>=skip+lim) return;} }
static int cmpS(const void*a,const void*b){const short*x=a,*y=b;for(int i=0;i<n;i++){if(x[i]!=y[i])return x[i]<y[i]?-1:1;}return 0;}
int main(int argc,char**argv){
  n=atoi(argv[1]); L=atoi(argv[2]); M=atoi(argv[3]); skip=atol(argv[6]); lim=atol(argv[7]);
  int U=2*M-2+L; out=fopen(argv[5],"ab");
  long next=0;
  if(skip==0 && argv[4][0]!='-'){
    FILE*f=fopen(argv[4],"rb"); long cap=1<<20, np=0; short*P=malloc(sizeof(short)*n*cap); short buf[MAXN];
    while(fread(buf,sizeof(short),n,f)==(size_t)n){ for(int i=0;i<n;i++){ if(i>0&&buf[i]==buf[i-1]) continue; short c[MAXN]; memcpy(c,buf,sizeof(short)*n); c[i]+=2*M-1; sortA(c); if(c[n-1]>U){ if(np==cap){cap*=2; short*q=malloc(sizeof(short)*n*cap); memcpy(q,P,sizeof(short)*n*np); free(P); P=q;} memcpy(P+n*np,c,sizeof(short)*n); np++; } } }
    fclose(f); qsort(P,np,sizeof(short)*n,cmpS); long u=0; for(long t=0;t<np;t++) if(u==0||cmpS(P+n*t,P+n*(u-1))) { if(u!=t) memcpy(P+n*u,P+n*t,sizeof(short)*n); u++; }
    for(long t=0;t<u;t++) test(P+n*t); next=u; }
  long dext=ndef, eib=nib, enon=nonib; idx=0;
  if((long)n*U>=(long)M*M) bal(0,M*M,L,U);
  int done = idx<skip+lim;
  printf("n=%d L=%d m=%d ext_tested=%ld ext_def=%ld bal_range=[%ld,%ld) deficient=%ld IB=%ld nonIB=%ld nodes=%ld %s\n",n,L,M,next,dext,skip,done?idx:skip+lim,ndef,nib,nonib,nodes,done?"DONE":"MORE");
  (void)eib;(void)enon; fclose(out); return 0; }
