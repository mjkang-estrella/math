/* CRIM (Column-Row Impartial Merge) normal-play P/N status for all partitions of size <= N.
   Move: delete one row (a part) or one column (subtract 1 from every part >= j, drop zeros).
   Reports every P-position with odd Dyson rank |r - lambda_1| (counterexamples to arXiv:2606.16828 Conjecture 1),
   and counts per size. No libc headers available: prototypes declared manually. */
int printf(const char*,...); void*calloc(unsigned long,unsigned long); int atoi(const char*);
typedef unsigned long long u64;
#define MAXN 100
static u64 P[MAXN+1][MAXN+1];      /* P[m][k] = #partitions of m with parts <= k */
static u64 off[MAXN+2];
static unsigned char *st;           /* 1 = P-position */
static u64 rank_(int*a,int len,int m){ /* a nonincreasing, sum m */
  u64 r=0; int k=m;
  for(int i=0;i<len;i++){ int x=a[i]; r+=P[m][x-1]; m-=x; (void)k; }
  return r;
}
static u64 idx(int*a,int len){ int m=0; for(int i=0;i<len;i++)m+=a[i]; return off[m]+rank_(a,len,m); }
static int N; static u64 cntP[MAXN+1], oddP[MAXN+1], printed=0;
static int cur[MAXN+1];
static void visit(int len,int m){
  int b[MAXN+1]; int win=0;
  /* row moves: distinct part values */
  for(int i=0;i<len && !win;i++){ if(i>0 && cur[i]==cur[i-1]) continue;
    int l=0; for(int j=0;j<len;j++) if(j!=i) b[l++]=cur[j];
    if(st[idx(b,l)]) win=1; }
  /* column moves: column j, 1<=j<=cur[0]; distinct effect when column lengths equal: column j length = #parts>=j */
  for(int j=1;j<=cur[0] && !win;j++){
    if(j>1){ int c1=0,c2=0; for(int t=0;t<len;t++){ if(cur[t]>=j)c1++; if(cur[t]>=j-1)c2++; } if(c1==c2) continue; }
    int l=0; for(int t=0;t<len;t++){ int x=cur[t]>=j?cur[t]-1:cur[t]; if(x>0) b[l++]=x; }
    if(st[idx(b,l)]) win=1; }
  u64 id=idx(cur,len);
  if(!win){ st[id]=1; cntP[m]++; int rk=len-cur[0]; if(rk<0)rk=-rk;
    if(rk&1){ oddP[m]++; if(printed<200){ printed++; printf("ODD-RANK P-POSITION size %d: [",m); for(int t=0;t<len;t++)printf("%d%s",cur[t],t+1<len?",":""); printf("]\n"); } } }
}
static void gen(int pos,int rem,int maxp,int m){
  if(rem==0){ visit(pos,m); return; }
  /* reverse-lex order not required since all smaller sizes are complete before size m */
  for(int x=(rem<maxp?rem:maxp);x>=1;x--){ cur[pos]=x; gen(pos+1,rem-x,x,m); }
}
int main(int argc,char**argv){
  N=atoi(argv[1]);
  for(int k=0;k<=N;k++)P[0][k]=1;
  for(int m=1;m<=N;m++){ P[m][0]=0; for(int k=1;k<=N;k++) P[m][k]=P[m][k-1]+(k<=m?P[m-k][k]:0); }
  off[0]=0; for(int m=0;m<=N;m++) off[m+1]=off[m]+P[m][m];
  st=calloc(off[N+1],1);
  st[0]=1; cntP[0]=1; /* empty partition: no move, P-position, rank 0 */
  for(int m=1;m<=N;m++){ gen(0,m,m,m); printf("size %d p=%llu P-positions=%llu oddrankP=%llu\n",m,P[m][m],cntP[m],oddP[m]); }
  return 0;
}
