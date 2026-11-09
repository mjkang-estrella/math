// MathDB 343098/343100/343101: graphs G(lambda, f) over F_p, f = X + a (deg 1) or X^3 + a (deg 3, p = 2 mod 3);
// edge x->y iff y^2 = f(x) or lambda*y^2 = f(x). lambda runs over N_p (non-squares, smaller of lambda, 1/lambda),
// a over F_p^*. Counts unconnected graphs U(p), the maximum number of components, and the component-size multiset.
int printf(const char*,...); int atoi(const char*); void*calloc(unsigned long,unsigned long); int fflush(void*);
typedef long long ll;
static ll pw(ll a,ll e,ll p){ll r=1;a%=p;while(e){if(e&1)r=r*a%p;a=a*a%p;e>>=1;}return r;}
static int *par;
static int find(int x){while(par[x]!=x){par[x]=par[par[x]];x=par[x];}return x;}
static void uni(int a,int b){a=find(a);b=find(b);if(a!=b)par[a]=b;}
int main(int argc,char**argv){
  int p=atoi(argv[1]),deg=atoi(argv[2]); int lo=argc>3?atoi(argv[3]):2, hi=argc>4?atoi(argv[4]):p; // lambda value range [lo,hi)
  int *sq=calloc(p,sizeof(int)); for(int i=0;i<p;i++)sq[i]=-1; for(int y=0;y<p;y++){int v=(int)((ll)y*y%p); if(sq[v]<0||y<sq[v])sq[v]=y;}
  par=calloc(p,sizeof(int)); int *cnt=calloc(p,sizeof(int)); int *fx=calloc(p,sizeof(int));
  long U=0,maxc=0,graphs=0; long sizehist[64]={0}; int big=0;
  for(int x=0;x<p;x++)fx[x]=(int)(deg==1?x:(ll)x*x%p*x%p);
  for(int lam=lo;lam<hi;lam++){ if(sq[lam]>=0)continue; int inv=(int)pw(lam,p-2,p); if(inv<lam)continue;
    for(int a=1;a<p;a++){ graphs++;
      for(int x=0;x<p;x++)par[x]=x;
      for(int x=0;x<p;x++){int v=(fx[x]+a)%p; int y; if(sq[v]>=0)y=sq[v]; else y=sq[(int)((ll)v*inv%p)]; uni(x,y); uni(x,(p-y)%p);}
      int nc=0; for(int x=0;x<p;x++)cnt[x]=0; for(int x=0;x<p;x++)cnt[find(x)]++;
      for(int x=0;x<p;x++)if(cnt[x])nc++;
      if(nc>1){U++; if(nc>maxc)maxc=nc; for(int x=0;x<p;x++)if(cnt[x]&&cnt[x]<p/2){if(cnt[x]<64)sizehist[cnt[x]]++; else big++;}}
    }}
  int L; int r=p%8; L=(r==1)?(p-1)/4:(r==3)?(p+1)/4:(r==5)?(p+3)/4:(p-3)/4;
  printf("lambda_range [%d,%d) ",lo,hi); printf("p %d deg %d graphs %ld U %ld L %d max_components %ld small_component_sizes:",p,deg,graphs,U,L,maxc);
  for(int s=1;s<64;s++)if(sizehist[s])printf(" %d:%ld",s,sizehist[s]); printf(" large_minor_components %d\n",big); fflush(0);
}
