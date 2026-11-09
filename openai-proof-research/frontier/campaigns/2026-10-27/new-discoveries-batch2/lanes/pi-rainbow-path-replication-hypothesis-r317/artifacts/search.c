/* Exact decision search for rho_R(P_n) sequence problem.
 *
 * Reduction (primary source, arXiv:1201.5340 Thm 2.1 + Lemma 2.2 [Lovasz]):
 * G ->_R P_n  iff  for every S subseteq [n]:  |S| <= max( max_{i in S} a_i ,
 *   max_{i,i+1 in S} (a_i + a_{i+1}) ),  where a_i = |clique_i|.
 * Equivalently for every k: the largest S with all a_i <= k-1 and no adjacent
 * pair (i,i+1) in S with a_i+a_{i+1} >= k has size <= k-1.  Computed exactly by
 * DP over the path (Lemma 6.1). This is an exact test over ALL proper colorings.
 *
 * Modes:
 *   verify <n> <a1> ... <an>   : check one sequence
 *   construction <n>           : print source's Thm 3.1 construction
 *   decide <n> <T>             : is there a feasible sequence with sum <= T?
 *                                DFS + exact pruning; prints FOUND seq or INFEASIBLE.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int N, T, found;
static int a[40];
static int dp0[40][40], dp1[40][40]; /* dp*[depth][k] */
static long long nodes;
static int g[40]; /* g[L] = sum_{j=1..L} ceil(j/2) */
static int best[40];

static void init_g(void){ int s=0; for(int L=0;L<40;L++){ g[L]=s; if(L<39) s+=(L+1+1)/2; } }
/* g[L] = sum_{j=1..L} ceil(j/2): g[0]=0,g[1]=1,g[2]=2,g[3]=4,g[4]=6,... */

/* extend DP state from depth i (prefix 1..i) by value v at i+1.
 * returns 0 if a bad set now exists entirely within prefix 1..i+1 */
static int extend(int i, int v){
    int ai = a[i];
    for(int k=2;k<=N;k++){
        int d0 = dp0[i][k] > dp1[i][k] ? dp0[i][k] : dp1[i][k];
        int d1 = -1;
        if(v <= k-1){
            d1 = d0 + 1;
            if(dp1[i][k] >= 0 && ai + v <= k-1) d1 = (dp1[i][k]+1 > d1) ? dp1[i][k]+1 : d1;
        }
        dp0[i+1][k]=d0; dp1[i+1][k]=d1;
        int m = d0>d1?d0:d1;
        if(m >= k) return 0;
    }
    a[i+1]=v;
    return 1;
}

static void dfs(int i, int sum){
    if(found) return;
    nodes++;
    if(sum + g[N-i] > T) return;
    if(i==N){
        found=1; memcpy(best,a+1,sizeof(int)*N); return;
    }
    int budget = T - sum - g[N-i-1];
    if(budget > N) budget = N;
    for(int v=1; v<=budget; v++){
        /* reversal symmetry: WLOG a_1 <= a_N */
        if(i+1==N && v < a[1]) continue;
        if(extend(i,v)) { dfs(i+1, sum+v); if(found) return; }
    }
}

static int feasible_le(int n, int Tt){
    N=n; T=Tt; found=0; nodes=0;
    a[0]=0;
    memset(dp0,-1,sizeof dp0); memset(dp1,-1,sizeof dp1);
    for(int k=0;k<40;k++){ dp0[0][k]=0; dp1[0][k]=-1; }
    dfs(0,0);
    return found;
}

static void construction(int n, int *out){
    /* Source Thm 3.1 constructions (verified against paper's n=13,15,16 examples) */
    int m4=n/4, r=n%4;
    int S1[40],T1[40],S2[40],T2[40];
    int l1=0,l2=0,l3=0,l4=0;
    if(r==0){
        for(int j=1;j<=m4;j++) S1[l1++]=j;
        for(int j=0;j<m4;j++) T1[l2++]=n/2;
        for(int j=m4+1;j<=n/2;j++) S2[l3++]=j;
        for(int j=0;j<m4-1;j++) T2[l4++]=n/4; T2[l4++]=n/2;
    } else if(r==1){
        int m=(n-1)/4;
        for(int j=1;j<=m+1;j++) S1[l1++]=j;
        for(int j=0;j<m;j++) T1[l2++]=m+1;
        for(int j=m+2;j<=2*m+1;j++) S2[l3++]=j;
        for(int j=0;j<m-1;j++) T2[l4++]=2*m+1; T2[l4++]=m+1;
    } else if(r==2){
        int m=(n-2)/4;
        for(int j=1;j<=m+1;j++) S1[l1++]=j;
        for(int j=0;j<m+1;j++) T1[l2++]=n/2;
        for(int j=m+2;j<=n/2;j++) S2[l3++]=j;
        for(int j=0;j<m;j++) T2[l4++]=m+1;
    } else {
        int m=(n-3)/4;
        for(int j=1;j<=m+1;j++) S1[l1++]=j;
        for(int j=0;j<m+1;j++) T1[l2++]=m+1;
        for(int j=m+2;j<=2*m+2;j++) S2[l3++]=j;
        for(int j=0;j<m;j++) T2[l4++]=2*m+2;
    }
    int p=0;
    int i1=0,i2=0,i3=0,i4=0;
    int len[4]={l1,l2,l3,l4};
    int idx=0;
    while(p<n){
        int w=idx%4;
        if(w==0&&i1<l1) out[p++]=S1[i1++];
        if(w==1&&i2<l2) out[p++]=T1[i2++];
        if(w==2&&i3<l3) out[p++]=S2[i3++];
        if(w==3&&i4<l4) out[p++]=T2[i4++];
        idx++;
    }
}

static int check_seq(int n, int *a){
    /* exact criterion, all k */
    N=n;
    for(int k=2;k<=n;k++){
        /* DP max bad set for level k */
        int d0=0,d1=-1;
        for(int i=1;i<=n;i++){
            int nd0 = d0 > d1 ? d0 : d1;
            int nd1 = -1;
            if(a[i] <= k-1){
                nd1 = nd0 + 1;
                if(d1 >= 0 && a[i-1] + a[i] <= k-1) nd1 = (d1+1>nd1)?d1+1:nd1;
            }
            d0=nd0; d1=nd1;
            if(i==n && (d0>=k || d1>=k)) return 0;
        }
    }
    return 1;
}

int main(int argc, char**argv){
    init_g();
    if(argc<2) return 2;
    if(!strcmp(argv[1],"verify")){
        int n=atoi(argv[2]);
        int arr[40]; for(int i=0;i<n;i++) arr[i]=atoi(argv[3+i]);
        int s=0; for(int i=0;i<n;i++) s+=arr[i];
        printf("n=%d sum=%d %s\n", n, s, check_seq(n,arr)?"FEASIBLE":"INFEASIBLE");
        return 0;
    }
    if(!strcmp(argv[1],"construction")){
        int n=atoi(argv[2]); int c[40]; construction(n,c);
        int s=0; for(int i=0;i<n;i++){printf("%d ",c[i]); s+=c[i];}
        printf("\nsum=%d feasible=%s\n", s, check_seq(n,c)?"YES":"NO");
        return 0;
    }
    if(!strcmp(argv[1],"decide")){
        int n=atoi(argv[2]), Tt=atoi(argv[3]);
        int ok=feasible_le(n,Tt);
        printf("n=%d T=%d nodes=%lld %s", n, Tt, nodes, ok?"FOUND":"INFEASIBLE");
        if(ok){ printf(" seq:"); for(int i=0;i<n;i++) printf(" %d", best[i]); }
        printf("\n");
        return 0;
    }
    return 2;
}
