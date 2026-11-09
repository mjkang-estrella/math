#include <bits/stdc++.h>
using namespace std;
int n,k,full;vector<int> nb, pw;vector<int8_t> memo;
bool win(int state,int turn){int ix=2*state+turn;if(memo[ix]>=0)return memo[ix]; vector<int> masks(k);int empty=0;for(int v=0;v<n;v++){int c=state/pw[v]%(k+1);if(!c)empty|=1<<v;else masks[c-1]|=1<<v;}
for(int b:nb)for(int c=0;c<k;c++)if(!(b&(masks[c]|empty)))return memo[ix]=0;
if(!empty)return memo[ix]=1;
int used=0;for(int c=0;c<k;c++)if(masks[c])used=c+1;
for(int v=0;v<n;v++)if(empty>>v&1)for(int c=1;c<=min(k,used+1);c++){bool w=win(state+c*pw[v],1-turn);if(w==!turn)return memo[ix]=w;}
return memo[ix]=turn;}
int main(int argc,char**argv){int maxn=argc>1?atoi(argv[1]):6;for(n=1;n<=maxn;n++){long long counts[8][8]={};int tested=0;for(int g=0;g<(1<<(n*(n-1)/2));g++){nb.resize(n);for(int i=0;i<n;i++)nb[i]=1<<i;int j=0;for(int a=0;a<n;a++)for(int b=a+1;b<n;b++,j++)if(g>>j&1){nb[a]|=1<<b;nb[b]|=1<<a;}int bound=n;for(int b:nb)bound=min(bound,(__builtin_popcount((unsigned)b)+2)/2);int val[2]={1,1};for(k=2;k<=bound;k++){pw.assign(n+1,1);for(int v=0;v<n;v++)pw[v+1]=pw[v]*(k+1);memo.assign(2*pw[n],-1);for(int t=0;t<2;t++)if(win(0,t))val[t]=k;}counts[val[0]][val[1]]++;tested++;if(abs(val[0]-val[1])>1){cout<<"COUNTEREXAMPLE "<<n<<" "<<g<<" "<<val[0]<<" "<<val[1]<<endl;return 0;}}
cout<<"n "<<n<<" tested "<<tested<<endl;for(int a=1;a<=n;a++)for(int b=1;b<=n;b++)if(counts[a][b])cout<<a<<","<<b<<":"<<counts[a][b]<<" ";cout<<endl;}}
