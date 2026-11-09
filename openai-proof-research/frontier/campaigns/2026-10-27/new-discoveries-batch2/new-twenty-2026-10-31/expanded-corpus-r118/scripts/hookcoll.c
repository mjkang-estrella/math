// For hook SYT of size n=N+1 with word w in {0,1}^N, mM_k = k! * V(w), V_tau = sum over occurrences of tau (|tau|=r=n-k-1) of first position.
// Find collisions V(w)=V(w') among all 2^N words. Usage: hookcoll r N
#include "libc.h"
typedef uint64_t u64;
static int r,N; static u64 W[1<<8]; static u64 R1[64],R2[64];
static void vec(u64 w,u64*out){ // patterns indexed by (len, bits): idx = (1<<len) + bits, len 1..r
  for(int i=0;i<(2<<r);i++) W[i]=0;
  for(int i=0;i<N;i++){ int x=(w>>i)&1;
    for(int len=r;len>=2;len--) for(int b=0;b<(1<<(len-1));b++){ int pat=(b<<1)|x; W[(1<<len)+pat]+=W[(1<<(len-1))+b]; }
    W[2+x]+= (u64)(i+1); }
  for(int b=0;b<(1<<r);b++) out[b]=W[(1<<r)+b]; }
typedef struct { u64 h1,h2,w; } E;
static int cmpe(const void*a,const void*b){ const E*x=a,*y=b; if(x->h1!=y->h1) return x->h1<y->h1?-1:1; if(x->h2!=y->h2) return x->h2<y->h2?-1:1; return 0; }
int main(int c,char**v){ r=atoi(v[1]); N=atoi(v[2]); u64 s=0x9E3779B97F4A7C15ULL; for(int i=0;i<64;i++){ s^=s<<13;s^=s>>7;s^=s<<17;R1[i]=s; s^=s<<13;s^=s>>7;s^=s<<17;R2[i]=s|1; }
  long M=1L<<N; E* e=malloc(sizeof(E)*M); u64 out[64],o2[64];
  for(long w=0;w<M;w++){ vec(w,out); u64 a=0,b=0; for(int t=0;t<(1<<r);t++){ a+=out[t]*R1[t]; b+=out[t]*R2[t]; } e[w].h1=a; e[w].h2=b; e[w].w=w; }
  qsort(e,M,sizeof(E),cmpe); long coll=0;
  for(long i=1;i<M;i++) if(!cmpe(&e[i],&e[i-1])){ vec(e[i].w,out); vec(e[i-1].w,o2); int eq=1; for(int t=0;t<(1<<r);t++) if(out[t]!=o2[t]) eq=0;
     if(eq){ coll++; if(coll<=4){ printf("  collision words (pos1..N, 1=leg):"); for(int j=0;j<N;j++) printf("%d",(int)((e[i-1].w>>j)&1)); printf(" "); for(int j=0;j<N;j++) printf("%d",(int)((e[i].w>>j)&1)); printf("\n"); } } }
  printf("r=%d (c=n-k=%d) N=%d (n=%d, k=%d): hook words=%ld exact-collisions(adjacent)=%ld\n",r,r+1,N,N+1,N-r,M,coll); return 0; }
