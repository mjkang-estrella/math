// Exhaustive check of Meszka-Pasotti-Pellegrini Conjecture (arXiv:2308.16553, conj:3):
// p odd prime, L multiset of p integers in [1,p-1]; perfect matching of K_{2p} (vertices Z_{2p}, length min(|u-w|,2p-|u-w|))
// with length list L exists iff #even entries of L is even.
// Usage: seating p [chunk nchunks]   -- enumerates multisets with even #evens (odd #evens impossible by Prop EvenNumber),
// orbit-reduced under multiplication by odd units of Z_{2p} (which preserve lengths' parity and length multiset structure).
#include "libc.h"
static int p,v,cnt[64],match_[128];
static long nodes=0; static long budget=50000000, unknown=0;static long tested=0,found=0,fails=0,skipped=0;
static int len_(int x){ x%=v; if(x<0)x+=v; return x<=v-x?x:v-x; }
static int bt(int left){
  nodes++; if(nodes>budget) return 0; if(!left) return 1;
  int a=0; while(match_[a]>=0) a++;
  int ord[64],no=0; for(int l=1;l<p;l++) if(cnt[l]) ord[no++]=l;
  for(int i=1;i<no;i++){int t=ord[i],j=i; while(j>0&&cnt[ord[j-1]]<cnt[t]){ord[j]=ord[j-1];j--;} ord[j]=t;}
  for(int oi=0;oi<no;oi++){ int l=ord[oi];
    int b1=(a+l)%v, b2=(a-l+v)%v;
    cnt[l]--;
    if(match_[b1]<0){ match_[a]=b1;match_[b1]=a; if(bt(left-1)){cnt[l]++;match_[a]=match_[b1]=-1;return 1;} match_[a]=match_[b1]=-1; }
    if(b2!=b1 && match_[b2]<0){ match_[a]=b2;match_[b2]=a; if(bt(left-1)){cnt[l]++;match_[a]=match_[b2]=-1;return 1;} match_[a]=match_[b2]=-1; }
    cnt[l]++;
  }
  return 0;
}
static int nu,units[64];
static int canonical(void){ // is cnt lexicographically minimal (as count vector over l=1..p-1) in its orbit?
  for(int k=0;k<nu;k++){ int u=units[k], img[64]; for(int l=1;l<p;l++) img[l]=0; for(int l=1;l<p;l++) img[len_(u*l)]+=cnt[l];
    for(int l=1;l<p;l++){ if(img[l]<cnt[l]) return 0; if(img[l]>cnt[l]) break; } }
  return 1;
}
static long chunk=0,nchunks=1,leafno=0;
static int smin=3,smax=3;
static void rec(int l,int rem,int evens){ int supp=0; for(int i=1;i<l;i++) supp+=cnt[i]>0; if(supp>smax) return; if(supp+(p-l)<smin && rem>0) {}

  if(l==p){ if(rem) return; if(evens&1) return; { int su=0; for(int i=1;i<p;i++) su+=cnt[i]>0; if(su<smin||su>smax) return; } leafno++; if(leafno%nchunks!=chunk) return;
    if(!canonical()){skipped++;return;}
    tested++; for(int i=0;i<v;i++) match_[i]=-1;
    nodes=0; if(bt(p)) found++; else if(nodes>budget){ unknown++; printf("BUDGET "); for(int i=1;i<p;i++) if(cnt[i]) printf(" %d^%d",i,cnt[i]); printf("\n"); } else { fails++; if(fails<=20){ printf("NO MATCHING for L ="); for(int i=1;i<p;i++) if(cnt[i]) printf(" %d^%d",i,cnt[i]); printf("\n"); fflush(stdout);} }
    return; }
  for(int c=(l==p-1?rem:0);c<=rem;c++){ cnt[l]=c; rec(l+1,rem-c,evens+((l%2==0)?c:0)); } cnt[l]=0;
}
int main(int argc,char**argv){ p=atoi(argv[1]); v=2*p; if(argc>3){chunk=atol(argv[2]);nchunks=atol(argv[3]);} if(argc>5){smin=atoi(argv[4]);smax=atoi(argv[5]);} if(argc>6) budget=atol(argv[6]);
  nu=0; for(int u=3;u<v;u+=2) if(u%p) { int r=len_(u); if(r==u||1) { int dup=0; for(int k=0;k<nu;k++) if(len_(units[k])==len_(u)) dup=1; if(!dup && len_(u)!=1) units[nu++]=u; } }
  rec(1,p,0);
  printf("p=%d chunk %ld/%ld: leaves(even #evens)=%ld orbit-skipped=%ld tested=%ld realizable=%ld NOT realizable=%ld budget-unknown=%ld support=[%d,%d]\n",p,chunk,nchunks,leafno,skipped,tested,found,fails,unknown,smin,smax); return 0; }
