// Tableau minors (arXiv:2307.13161). SYT encoded by Yamanouchi word (row of entry i, 4 bits each, i=1..s) -> u64 key.
// Level s arrays: keys sorted; index by binary search. child[s][t*s + (m-1)] = index in level s-1 of T - m.
// mode M n k  : multiset injectivity on YT(n) for k-minors via random linear hash (exact DP: h_s(T)=sum_m h_{s-1}(T-m)), collisions verified by second independent hash.
// mode S n k  : set injectivity via R min-hashes (union-compatible), then exact verification of signature-collision groups by explicit enumeration.
#include "libc.h"
typedef uint64_t u64;
static int NMAX; static u64* keys[20]; static long cnt[20]; static int* child[20];
static u64 rng=88172645463325252ULL; static u64 xs(void){ rng^=rng<<13; rng^=rng>>7; rng^=rng<<17; return rng; }
static long findk(int s,u64 key){ long lo=0,hi=cnt[s]-1; while(lo<=hi){ long mid=(lo+hi)/2; if(keys[s][mid]==key) return mid; if(keys[s][mid]<key) lo=mid+1; else hi=mid-1;} return -1; }
static int cmpu(const void*a,const void*b){ u64 x=*(const u64*)a,y=*(const u64*)b; return x<y?-1:x>y; }
// decode key into grid
static void decode(int s,u64 key,int g[16][16],int rl[16]){ for(int i=0;i<16;i++) rl[i]=0; for(int e=1;e<=s;e++){ int r=(key>>(4*(e-1)))&15; g[r][rl[r]++]=e; } }
static u64 encode(int s,int g[16][16],int rl[16]){ u64 k=0; for(int r=0;r<16;r++) for(int j=0;j<rl[r];j++){ int e=g[r][j]; k|=(u64)r<<(4*(e-1)); } return k; }
static u64 del(int s,u64 key,int m){ int g[16][16],rl[16]; decode(s,key,g,rl); int i=(key>>(4*(m-1)))&15, j=0; while(g[i][j]!=m) j++;
  for(;;){ int right=(j+1<rl[i])?g[i][j+1]:0; int below=(i+1<16 && j<rl[i+1])?g[i+1][j]:0;
    if(!right&&!below) break; if(!below || (right && right<below)){ g[i][j]=right; j++; } else { g[i][j]=below; i++; } }
  rl[i]--; for(int r=0;r<16;r++) for(int c=0;c<rl[r];c++) if(g[r][c]>m) g[r][c]--; return encode(s-1,g,rl); }
static void build(int nmax){ keys[0]=malloc(8); keys[0][0]=0; cnt[0]=1;
  for(int s=1;s<=nmax;s++){ long cap=cnt[s-1]*s+1; u64* out=malloc(cap*8); long no=0;
    for(long t=0;t<cnt[s-1];t++){ int g[16][16],rl[16]; decode(s-1,keys[s-1][t],g,rl);
      for(int r=0;r<16;r++){ if(r>0 && rl[r]>=rl[r-1]) continue; out[no++]=keys[s-1][t] | ((u64)r<<(4*(s-1))); if(rl[r]==0) break; } }
    qsort(out,no,8,cmpu); long w=0; for(long i=0;i<no;i++) if(!w||out[i]!=out[w-1]) out[w++]=out[i]; keys[s]=out; cnt[s]=w; }
  for(int s=1;s<=nmax;s++){ child[s]=malloc(sizeof(int)*cnt[s]*s); for(long t=0;t<cnt[s];t++) for(int m=1;m<=s;m++) child[s][t*s+m-1]=(int)findk(s-1,del(s,keys[s][t],m)); } }
typedef struct { u64 h[2]; long id; } HR;
static int cmphr(const void*a,const void*b){ const HR*x=a,*y=b; if(x->h[0]!=y->h[0]) return x->h[0]<y->h[0]?-1:1; if(x->h[1]!=y->h[1]) return x->h[1]<y->h[1]?-1:1; return 0; }
static void multiset(int n,int k){ HR* r=malloc(sizeof(HR)*cnt[n]); u64 *h0=0,*h1=0;
  for(int pass=0;pass<2;pass++){ int base=n-k; u64* h=malloc(8*cnt[base]); for(long i=0;i<cnt[base];i++) h[i]=xs();
    for(int s=base+1;s<=n;s++){ u64* hn=malloc(8*cnt[s]); for(long t=0;t<cnt[s];t++){ u64 a=0; for(int m=0;m<s;m++) a+=h[child[s][t*s+m]]; hn[t]=a; } free(h); h=hn; }
    if(pass==0) h0=h; else h1=h; }
  for(long t=0;t<cnt[n];t++){ r[t].h[0]=h0[t]; r[t].h[1]=h1[t]; r[t].id=t; } qsort(r,cnt[n],sizeof(HR),cmphr);
  long dup=0; for(long i=1;i<cnt[n];i++) if(cmphr(&r[i],&r[i-1])==0){ dup++; if(dup<=12) printf("  multiset-collision keys %llx %llx\n",(unsigned long long)keys[n][r[i-1].id],(unsigned long long)keys[n][r[i].id]); }
  printf("MULTI n=%d k=%d |YT|=%ld duplicates=%ld -> %s\n",n,k,cnt[n],dup,dup?"NOT injective":"injective"); fflush(stdout); free(r); free(h0); free(h1); }
// exact set of k-minors of T (level n index t) as sorted unique ids at level n-k
static long exact_set(int n,int k,long t,int* buf){ long cur_n=1; int* cur=malloc(sizeof(int)*1); cur[0]=(int)t; int s=n;
  for(int step=0;step<k;step++){ int* nx=malloc(sizeof(int)*cur_n*s); long nn=0; for(long i=0;i<cur_n;i++) for(int m=0;m<s;m++) nx[nn++]=child[s][(long)cur[i]*s+m];
    // unique
    for(long i=1;i<nn;i++){ int x=nx[i],j=i; while(j>0&&nx[j-1]>x){nx[j]=nx[j-1];j--;} nx[j]=x; }
    long w=0; for(long i=0;i<nn;i++) if(!w||nx[i]!=nx[w-1]) nx[w++]=nx[i]; free(cur); cur=nx; cur_n=w; s--; }
  for(long i=0;i<cur_n;i++) buf[i]=cur[i]; free(cur); return cur_n; }
#define R 6
typedef struct { u64 h[R]; long id; } SR;
static int cmpsr(const void*a,const void*b){ const SR*x=a,*y=b; for(int i=0;i<R;i++) if(x->h[i]!=y->h[i]) return x->h[i]<y->h[i]?-1:1; return 0; }
static void setmode(int n,int k){ int base=n-k; SR* r=malloc(sizeof(SR)*cnt[n]);
  for(int q=0;q<R;q++){ u64* h=malloc(8*cnt[base]); for(long i=0;i<cnt[base];i++) h[i]=xs();
    for(int s=base+1;s<=n;s++){ u64* hn=malloc(8*cnt[s]); for(long t=0;t<cnt[s];t++){ u64 a=~(u64)0; for(int m=0;m<s;m++){ u64 c=h[child[s][t*s+m]]; if(c<a)a=c; } hn[t]=a; } free(h); h=hn; }
    for(long t=0;t<cnt[n];t++){ r[t].h[q]=h[t]; r[t].id=t; } free(h); }
  qsort(r,cnt[n],sizeof(SR),cmpsr);
  long cand=0,truedup=0; int *b1=malloc(sizeof(int)*4000000),*b2=malloc(sizeof(int)*4000000);
  for(long i=0;i<cnt[n];){ long j=i+1; while(j<cnt[n] && cmpsr(&r[j],&r[i])==0) j++;
    if(j-i>1){ cand+=j-i; for(long x=i;x<j;x++){ long a=exact_set(n,k,r[x].id,b1); for(long y=x+1;y<j;y++){ long b=exact_set(n,k,r[y].id,b2); int eq=(a==b); for(long z=0;eq&&z<a;z++) if(b1[z]!=b2[z]) eq=0;
        if(eq){ truedup++; if(truedup<=5) printf("  SET-EQUAL pair keys %llx %llx (|M_k|=%ld)\n",(unsigned long long)keys[n][r[x].id],(unsigned long long)keys[n][r[y].id],a); } } } }
    i=j; }
  printf("SET n=%d k=%d |YT|=%ld signature-group-members=%ld exact-equal-pairs=%ld -> %s\n",n,k,cnt[n],cand,truedup,truedup?"NOT injective":(cand?"injective (all candidates refuted exactly)":"injective")); fflush(stdout); free(r); }
int main(int argc,char**argv){ char mode=argv[1][0]; int n=atoi(argv[2]); int kmin=atoi(argv[3]), kmax=atoi(argv[4]); build(n);
  printf("built YT(0..%d): last=%ld\n",n,cnt[n]); for(int k=kmin;k<=kmax;k++){ if(mode=='M') multiset(n,k); else setmode(n,k); } return 0; }
