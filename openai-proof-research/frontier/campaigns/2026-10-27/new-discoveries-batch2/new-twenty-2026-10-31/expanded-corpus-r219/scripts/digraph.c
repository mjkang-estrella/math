extern int printf(const char*,...); extern int puts(const char*); extern int atoi(const char*);
int n,A[16],full;unsigned long long leaves,nd,sc,nc,found;
int strong(int S){int r=S&-S,t;do{t=r;for(int i=0;i<n;i++)if(r>>i&1)t|=A[i]&S;if(t==r)break;r=t;}while(1);if(r!=S)return 0;r=S&-S;do{t=r;for(int i=0;i<n;i++)if((S>>i&1)&&(A[i]&r))t|=1<<i;if(t==r)break;r=t;}while(1);return r==S;}
int acyclic(int S){while(S){int rem=0;for(int i=0;i<n;i++)if((S>>i&1)&&!(A[i]&S))rem|=1<<i;if(!rem)return 0;S^=rem;}return 1;}
void check(){leaves++;int in[16]={0};for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(A[i]>>j&1)in[j]++;for(int i=0;i<n;i++)if(in[i]<2)return;nd++;for(int i=0;i<n;i++){int ins=0;for(int j=0;j<n;j++)if(A[j]>>i&1)ins|=1<<j;if(acyclic(A[i])||acyclic(ins))return;}nc++;if(!strong(full))return;sc++;for(int S=1;S<full;S++)if(__builtin_popcount((unsigned)(full^S))>=2&&acyclic(S)&&!strong(full^S))return;found++;printf("WITNESS ");for(int i=0;i<n;i++)printf("%d,",A[i]);puts("");}
void dfs(int i,int m){if(i==n){check();return;}for(int S=0;S<=full;S++)if(!(S>>i&1)){int d=__builtin_popcount((unsigned)S);if(d>=2&&m+d+2*(n-i-1)<3*n-3){A[i]=S;dfs(i+1,m+d);}}}
int main(int argc,char**argv){n=atoi(argv[1]);full=(1<<n)-1;dfs(0,0);printf("n %d leaves %llu indegree>=2 %llu neighborhood_cyclic %llu strong %llu counterexamples %llu\n",n,leaves,nd,nc,sc,found);}
