/* Check arXiv:2605.26916 Conjecture 4.9 for all preorders of size n (with repetition: naturally labelled posets on k vertices
   x compositions of n into k vertex sizes).  P_tau = {a in N^E : sum_{e in I} a_e <= |I| for every order ideal I}, ordered
   componentwise, rank |a|.  F(m) = sum over multichains p1<=...<=p_{m-1} of q^{sum ranks} = Z_q(P,[m]_q).  F(m) = G(q^m) with G
   a polynomial of degree <= R (max rank); interpolate G at X=q^m, m=2..R+3 (extra point checks consistency), then
   LHS = G(q^{-1}) = Z_q(P,[-1]_q) (since [-1]_q=-1/q and [m]_q=(q^m-1)/(q-1)).  RHS = (-1)^n sum_{a in Max P} q^{-cov(a)},
   cov(a) = #nonzero coordinates (P is down-closed).  All arithmetic mod prime p at a fixed random q. */
int printf(const char*,...); int atoi(const char*); int fflush(void*); void*calloc(unsigned long,unsigned long); void free(void*);
typedef unsigned long long u64; typedef unsigned __int128 u128;
static const u64 MOD=2305843009213693951ULL; /* 2^61-1 */
static u64 mm(u64 a,u64 b){ u128 r=(u128)a*b; u64 lo=(u64)(r&MOD), hi=(u64)(r>>61); u64 s=lo+hi; if(s>=MOD)s-=MOD; return s; }
static u64 ad(u64 a,u64 b){ u64 s=a+b; if(s>=MOD)s-=MOD; return s; }
static u64 sb(u64 a,u64 b){ return a>=b?a-b:a+MOD-b; }
static u64 pw(u64 a,u64 e){ u64 r=1; while(e){ if(e&1)r=mm(r,a); a=mm(a,a); e>>=1;} return r; }
static u64 inv(u64 a){ return pw(a,MOD-2); }
static int n,K; static int below[16]; /* below[v] bitmask of vertices < v in poset (strict), naturally labelled */
static int vsz[16];
static int idealmask[70000]; static int nideal;
static unsigned char *pt; /* membership array over (n+1)^n */
static int base_pow[16];
static int *pts; static int npts; static int ptsCap;
static u64 Q, Qi; static u64 qp[64];
static long long nPre=0, nFail=0, nIncons=0;
static int elemv[16]; /* vertex of element */
static int S[16];
/* enumerate order ideals of poset on K vertices: subsets closed downward */
static void ideals(void){ nideal=0; for(int s=0;s<(1<<K);s++){ int ok=1; for(int v=0;v<K&&ok;v++) if((s>>v)&1) if((below[v]&s)!=below[v]) ok=0; if(ok) idealmask[nideal++]=s; } }
static int a_[16];
static void addpt(void){ int code=0; for(int e=0;e<n;e++) code+=a_[e]*base_pow[e]; if(npts>=ptsCap){ printf("cap\n"); return;} pts[npts++]=code; pt[code]=1; }
static void distribute(int v,int e0){ /* distribute S[v] among elements of vertex v, then next vertex */
  (void)e0; }
static int elist[16][16], ecount[16];
static void dist(int v,int idx,int rem){
  if(v==K){ addpt(); return; }
  int e=elist[v][idx];
  if(idx==ecount[v]-1){ a_[e]=rem; dist(v+1,0,S[v+1<K?v+1:0]*(v+1<K)); return; }
  for(int x=0;x<=rem;x++){ a_[e]=x; dist(v,idx+1,rem-x); }
}
static int byMax[16][4096], nByMax[16];
static void genS(int v){
  if(v==K){ dist(0,0,S[0]); return; }
  for(int x=0;x<=n;x++){ S[v]=x; int bad=0;
    for(int i=0;i<nByMax[v]&&!bad;i++){ int s=byMax[v][i], sum=0, cap=0; for(int u=0;u<=v;u++) if((s>>u)&1){ sum+=S[u]; cap+=vsz[u]; } if(sum>cap) bad=1; }
    if(bad) break; /* sums only grow with x */
    genS(v+1); }
}
static u64 *f,*g;
static long long shardCtr=0; static int SH=0, NSH=1;
static void process(void){
  if((shardCtr++)%NSH!=SH) return;
  nPre++;
  /* element lists */
  int e=0; for(int v=0;v<K;v++){ ecount[v]=vsz[v]; for(int j=0;j<vsz[v];j++){ elist[v][j]=e; elemv[e]=v; e++; } }
  ideals(); for(int v=0;v<K;v++) nByMax[v]=0; for(int i=0;i<nideal;i++){ int sm=idealmask[i]; if(!sm) continue; int mx=31-__builtin_clz(sm); byMax[mx][nByMax[mx]++]=sm; } npts=0; genS(0);
  /* sort pts by rank (counting sort) */
  int R=0; static int rk[200000]; static int order[200000]; int cnt[64]={0};
  for(int i=0;i<npts;i++){ int c=pts[i],r=0; for(int t=0;t<n;t++){ r+=c%(n+1); c/=(n+1);} rk[i]=r; if(r>R)R=r; cnt[r]++; }
  int st[65]; st[0]=0; for(int r=0;r<=R;r++) st[r+1]=st[r]+cnt[r];
  for(int i=0;i<npts;i++) order[st[rk[i]]++]=i;
  /* index map code->position */
  static int *pos=0; if(!pos) pos=calloc(43046721+10,4);
  for(int i=0;i<npts;i++) pos[pts[order[i]]]=i;
  int M=R+3; u64 Fm[70];
  for(int i=0;i<npts;i++) f[i]=qp[rk[order[i]]];
  Fm[2]=0; for(int i=0;i<npts;i++) Fm[2]=ad(Fm[2],f[i]);
  static int nbr[16][200000];
  for(int t=0;t<n;t++) for(int i=0;i<npts;i++){ int c=pts[order[i]]; int dig=(c/base_pow[t])%(n+1); nbr[t][i]= dig>0 ? pos[c-base_pow[t]] : -1; }
  for(int m=3;m<=M+1;m++){
    for(int i=0;i<npts;i++) g[i]=f[i];
    for(int t=0;t<n;t++){ int *nb=nbr[t]; for(int i=0;i<npts;i++){ int j=nb[i]; if(j>=0) g[i]=ad(g[i],g[j]); } }
    for(int i=0;i<npts;i++) f[i]=mm(g[i],qp[rk[order[i]]]);
    Fm[m]=0; for(int i=0;i<npts;i++) Fm[m]=ad(Fm[m],f[i]);
  }
  /* interpolate G of degree <= R through X_m=q^m, m=2..R+2 (R+1 points) and check m=R+3 (and R+4) */
  int D=R+1; u64 X[70];
  for(int j=0;j<D;j++) X[j]=pw(Q,2+j);
  static u64 invden[70][70]; static int haveD[70];
  if(!haveD[D]){ for(int j=0;j<D;j++){ u64 den=1; for(int l=0;l<D;l++) if(l!=j) den=mm(den,sb(X[j],X[l])); invden[D][j]=inv(den);} haveD[D]=1; }
  #define LAG(x,res) { u64 s=0; for(int j=0;j<D;j++){ u64 num=1; for(int l=0;l<D;l++) if(l!=j){ num=mm(num,sb((x),X[l])); } s=ad(s,mm(Fm[2+j],mm(num,invden[D][j]))); } res=s; }
  u64 chk; LAG(pw(Q,2+D),chk); u64 chk2; LAG(pw(Q,3+D),chk2);
  if(chk!=Fm[2+D] || chk2!=Fm[3+D]){ nIncons++; }
  u64 lhs; LAG(Qi,lhs);
  /* RHS */
  u64 rhs=0;
  for(int i=0;i<npts;i++){ int c=pts[i]; int maximal=1; int cov=0; for(int t=0;t<n;t++){ int dig=(c/base_pow[t])%(n+1); if(dig>0) cov++; if(dig<n && pt[c+base_pow[t]]) maximal=0; } if(maximal) rhs=ad(rhs,pw(Qi,cov)); }
  if(n&1) rhs=sb(0,rhs);
  if(lhs!=rhs){ nFail++; if(nFail<=20){ printf("FAIL n=%d K=%d sizes",n,K); for(int v=0;v<K;v++)printf(" %d",vsz[v]); printf(" below"); for(int v=0;v<K;v++)printf(" %d",below[v]); printf(" |P|=%d R=%d\n",npts,R); fflush(0);} }
  for(int i=0;i<npts;i++) pt[pts[i]]=0;
}
static void comps(int v,int rem){ if(v==K-1){ vsz[v]=rem; process(); return; } for(int x=1;x<=rem-(K-1-v);x++){ vsz[v]=x; comps(v+1,rem-x); } }
static void posets(int v){
  if(v==K){ comps(0,n); return; }
  /* choose strict down-set of new vertex v: an order ideal of current poset on 0..v-1 */
  for(int s=0;s<(1<<v);s++){ int ok=1; for(int u=0;u<v&&ok;u++) if((s>>u)&1) if((below[u]&s)!=below[u]) ok=0; if(!ok) continue; below[v]=s; posets(v+1); }
}
int main(int argc,char**argv){
  n=atoi(argv[1]); int k0=atoi(argv[2]), k1=atoi(argv[3]); if(argc>5){ SH=atoi(argv[4]); NSH=atoi(argv[5]); }
  Q=1234567891011ULL%MOD; Qi=inv(Q); qp[0]=1; for(int i=1;i<64;i++) qp[i]=mm(qp[i-1],Q);
  base_pow[0]=1; for(int i=1;i<=n;i++) base_pow[i]=base_pow[i-1]*(n+1);
  pt=calloc(base_pow[n]+10,1); ptsCap=200000; pts=calloc(ptsCap,4); f=calloc(ptsCap,8); g=calloc(ptsCap,8);
  for(K=k0;K<=k1;K++){ long long before=nPre; posets(0); printf("n=%d K=%d preorders(with repetition)=%lld fails=%lld inconsistent_interp=%lld\n",n,K,nPre-before,nFail,nIncons); fflush(0); }
  return 0;
}
