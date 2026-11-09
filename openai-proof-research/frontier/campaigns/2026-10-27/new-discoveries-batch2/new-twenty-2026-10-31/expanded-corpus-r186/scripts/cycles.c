extern int printf(const char*,...); extern int fflush(void*); extern int atoi(const char*); extern void* memcpy(void*,const void*,unsigned long); extern void* memset(void*,int,unsigned long);
long long counts[32],totals[32];int N,pat;
int cyclic(int*p,int n){int j=0;for(int k=0;k<n;k++){j=p[j];if(j==0)return k==n-1;}return 0;}
int allowed(int*p,int n,int at){
 if(pat==123){int low=100;for(int i=0;i<at;i++){if(p[i]>low)return 0;if(p[i]<low)low=p[i];}}
 if(pat==321){int high=-1;for(int i=at;i<n;i++){if(p[i]<high)return 0;if(p[i]>high)high=p[i];}}
 if(pat==132 || pat==231){int lo=100,hi=-1;for(int i=0;i<at;i++){if(p[i]<lo)lo=p[i];if(p[i]>hi)hi=p[i];}for(int i=at;i<n;i++){if(pat==132 && lo<p[i])return 0;if(pat==231 && hi>p[i])return 0;}}
 return 1;}
void dfs(int*p,int n){totals[n]++;if(n && cyclic(p,n))counts[n]++;if(n==N)return;for(int at=0;at<=n;at++)if(allowed(p,n,at)){int q[32];memcpy(q,p,at*sizeof(int));q[at]=n;memcpy(q+at+1,p+at,(n-at)*sizeof(int));dfs(q,n+1);}}
int main(int argc,char**argv){N=atoi(argv[1]);int patterns[]={123,132,231,321};for(int j=0;j<4;j++){pat=patterns[j];if(argc>2 && pat!=atoi(argv[2]))continue;memset(counts,0,sizeof(counts));memset(totals,0,sizeof(totals));int p[32];dfs(p,0);for(int n=1;n<=N;n++)printf("%d %d %lld %lld\n",pat,n,totals[n],counts[n]);fflush((void*)0);}}
