/* Screen binary words w of length k (Kmin..Kmax) for rho^w = 1/2 without balanced borders (arXiv:2606.06655 Conj. 6.1).
   Borders B(w,w) = prefixes p of w (length j=1..k, including w) that are also suffixes.
   E(z) = (z-2)*sum_b z^{|b|-1} + 1, lambda = largest real root (in (1,2]).  rho=1/2 iff P(lambda)=0, P(z)=sum_b (2|b|_1-|b|) z^{|b|}.
   Prints candidates with |P(lambda)|/max|term| < 1e-12 (long double), and only first word of each signature. Words with w[0]=1 only (bit-flip symmetry: rho^{flip w}=1-rho^w). */
int printf(const char*,...); int atoi(const char*); int fflush(void*); void*calloc(unsigned long,unsigned long);
#define HS (1ULL<<26)
static unsigned long long *H;
typedef long double LD;
static LD fabsl_(LD x){return x<0?-x:x;}
int main(int argc,char**argv){
  int K0=atoi(argv[1]),K1=atoi(argv[2]);
  H=calloc(HS,8);
  for(int k=K0;k<=K1;k++){
    for(unsigned long long q=0;q<HS;q++)H[q]=0;
    unsigned long long total=0,unbal=0,cand=0,distinct=0;
    for(unsigned long long m=0;m<(1ULL<<(k-1));m++){
      int w[64]; w[0]=1; for(int i=1;i<k;i++) w[i]=(m>>(i-1))&1;
      /* KMP failure function */
      int f[65]; f[0]=-1; f[1]=0; int pre[65]; pre[0]=0; for(int i=0;i<k;i++) pre[i+1]=pre[i]+w[i];
      for(int i=1;i<k;i++){ int j=f[i]; while(j>=0 && w[j]!=w[i]) j=f[j]; f[i+1]=j+1; }
      /* borders: k, f[k], f[f[k]], ... >0 */
      int bl[64],nb=0; int j=k; while(j>0){ bl[nb++]=j; j=f[j]; }
      total++;
      int bal=1; for(int t=0;t<nb;t++) if(2*pre[bl[t]]!=bl[t]) bal=0;
      if(bal) continue; unbal++;
      { unsigned long long h=1469598103934665603ULL; for(int t=0;t<nb;t++){ h^=(unsigned long long)(bl[t]*131+pre[bl[t]]); h*=1099511628211ULL; } h|=1; unsigned long long q=h&(HS-1); int seen=0; while(H[q]){ if(H[q]==h){seen=1;break;} q=(q+1)&(HS-1);} if(seen) continue; H[q]=h; distinct++; }
      /* lambda: largest real root of E on (1,2]; E(2)=1>0; E(z) -> leading z^k so positive for large z. find root by scanning downward then bisection */
      LD lo=1.0L,hi=2.0L; /* E(1)=1-nb <=0 when nb>=1; if nb==1, E(1)=0 root at 1 but lambda>1 is the largest root */
      /* evaluate E */
      #define EVAL(z,res) { LD s=0; for(int t=0;t<nb;t++){ LD p=1; for(int e=0;e<bl[t]-1;e++) p*=(z); s+=p; } res=((z)-2)*s+1; }
      /* scan from 2 downward to find sign change */
      LD prev=2.0L, Ep; EVAL(prev,Ep); LD root=-1;
      for(int s=1;s<=1024;s++){ LD z=2.0L-s*(1.0L/1024); LD Ez; EVAL(z,Ez); if((Ez<=0)!=(Ep<=0)){ lo=z;hi=prev; root=0; break;} prev=z;Ep=Ez; }
      if(root<0){ printf("NOROOT k=%d m=%llu\n",k,m); continue; }
      for(int it=0;it<200;it++){ LD mid=(lo+hi)/2, Em, El; EVAL(mid,Em); EVAL(lo,El); if((Em<=0)==(El<=0)) lo=mid; else hi=mid; }
      LD lam=(lo+hi)/2, P=0, mx=0;
      for(int t=0;t<nb;t++){ LD p=1; for(int e=0;e<bl[t];e++) p*=lam; LD term=(2*pre[bl[t]]-bl[t])*p; P+=term; if(fabsl_(term)>mx) mx=fabsl_(term); }
      if(fabsl_(P)<1e-12L*mx){ cand++; printf("CAND k=%d w=",k); for(int i=0;i<k;i++)printf("%d",w[i]); printf(" lambda=%.18Lf P=%Le borders:",lam,P); for(int t=0;t<nb;t++)printf(" (%d,%d)",bl[t],pre[bl[t]]); printf("\n"); fflush(0);}
    }
    printf("k=%d words(w0=1)=%llu non-balanced-border=%llu distinct-signatures=%llu candidates=%llu\n",k,total,unbal,distinct,cand); fflush(0);
  }
  return 0;
}
