/* arXiv:2606.21532 Conj 4.17 screen. For a partition lambda (multiset of multiplicities), enumerate s in S^2(lambda):
   nondecreasing integer sequences of length n=|lambda| with values in [0,2n-2], prefix sums >= t(t-1), total n(n-1),
   whose distinct values have multiplicities forming lambda.  For each: (1) deficiency test (source Lemma 4.2/4.3);
   (2) if not deficient and mode>=1: backtracking search for phi in S_n with multiset {i+phi(i)} = s.
   Prints any s in S^2(lambda) not realised (incompleteness witness).  usage: xray mode part1 part2 ... */
int printf(const char*,...); int atoi(const char*); int fflush(void*);
static int n, np, parts[64], used[64], seq[64], mode;
static unsigned long long cnt=0, defic=0, unreal=0, real_=0, nodes=0; static unsigned long long nodecap=2000000000ULL;
static int need[200]; static int taken[64];
static int bt(int i){ /* assign phi(i) for i in decreasing order of constraint: simple order i=n-1..0 */
  if(i<0) return 1; nodes++; if(nodes>nodecap) return -1;
  for(int j=n-1;j>=0;j--){ if(taken[j]) continue; int c=i+j; if(!need[c]) continue;
    need[c]--; taken[j]=1; int r=bt(i-1); need[c]++; taken[j]=0; if(r) return r; }
  return 0;
}
static void check(void){
  cnt++;
  int M=seq[n-1];
  int def=0;
  for(int d=0;d<n && !def;d++){ int sg=0; for(int i=0;i<n;i++) if(seq[i]<=d) sg++; int mx=2*d+2>M+1?2*d+2:M+1; if(n+sg>mx) def=1; }
  if(def){ defic++; if(defic<=20){ printf("DEFICIENT:"); for(int i=0;i<n;i++)printf(" %d",seq[i]); printf("\n"); fflush(0);} return; }
  if(mode<1) return;
  for(int c=0;c<=2*n;c++) need[c]=0; for(int i=0;i<n;i++) need[seq[i]]++;
  for(int j=0;j<n;j++) taken[j]=0;
  nodes=0; int r=bt(n-1);
  if(r==1) real_++; else { unreal++; printf("%s:",r<0?"UNDECIDED":"UNREALISABLE"); for(int i=0;i<n;i++)printf(" %d",seq[i]); printf("\n"); fflush(0); }
}
static void dfs(int t,int sum,int last){
  if(t==n){ if(sum==n*(n-1)) check(); return; }
  for(int v=last+1; v<=2*n-2; v++){
    for(int p=0;p<np;p++){ if(used[p]) continue; int dup=0; for(int q=0;q<p;q++) if(!used[q]&&parts[q]==parts[p]) dup=1; if(dup) continue;
      int m=parts[p]; int ok=1, s=sum;
      for(int k=0;k<m;k++){ seq[t+k]=v; s+=v; int tt=t+k+1; if(s<tt*(tt-1)) {ok=0;break;} }
      if(!ok) continue;
      if(s> n*(n-1)) continue;
      /* remaining terms are > v: need s + (n-t-m)*(v+1) <= n(n-1) roughly */
      if(s + (long)(n-t-m)*(v+1) > (long)n*(n-1)) continue;
      if(s + (long)(n-t-m)*(2*n-2) < (long)n*(n-1)) continue;
      used[p]=1; dfs(t+m,s,v); used[p]=0; }
  }
}
int main(int argc,char**argv){
  mode=atoi(argv[1]); np=argc-2; n=0; for(int i=0;i<np;i++){ parts[i]=atoi(argv[i+2]); n+=parts[i]; }
  /* sort parts descending for dedupe */
  for(int i=0;i<np;i++)for(int j=i+1;j<np;j++) if(parts[j]>parts[i]){int x=parts[i];parts[i]=parts[j];parts[j]=x;}
  dfs(0,0,-1);
  printf("lambda=["); for(int i=0;i<np;i++)printf("%d%s",parts[i],i+1<np?",":""); printf("] n=%d |S2(lambda)|=%llu deficient=%llu realised=%llu unrealised_or_undecided=%llu\n",n,cnt,defic,real_,unreal);
  return 0;
}
