#include <iostream>
#include <vector>
#include <cstdint>
using namespace std;
int main(){
 for(int n=1;n<=7;n++){
 vector<pair<int,int>> es;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)es.push_back({i,j});
 long long tf=0,connected=0,noncb=0,minslack=1000000000,maxsigma=-1;long long B=0;
 for(int a=1;a<n;a++) B=max(B,1LL*a*(n-a)*(n-2*a)*(n-2*a));
 for(uint64_t mask=0;mask<(1ULL<<es.size());mask++){
 int adj[7]={},deg[7]={},m=0;bool tri=false;
 for(int k=0;k<(int)es.size();k++)if(mask>>k&1){auto [u,v]=es[k]; if(adj[u]&adj[v]){tri=true;break;}adj[u]|=1<<v;adj[v]|=1<<u;deg[u]++;deg[v]++;m++;}
 if(tri)continue;tf++;int reach=1;for(int z=0;z<n;z++)for(int u=0;u<n;u++)if(reach>>u&1)reach|=adj[u];if(reach!=(1<<n)-1)continue;connected++;
 long long M=0;for(int u=0;u<n;u++)M+=deg[u]*deg[u];long long D=1LL*n*m-M,s=1LL*n*M-4LL*m*m;maxsigma=max(maxsigma,s);
 if(D){noncb++;minslack=min(minslack,D-(n-2));if(D<n-2){cerr<<"GAP FAILURE "<<n<<' '<<mask<<endl;return 1;}}
 if(s>B){cerr<<"CONJECTURE FAILURE "<<n<<' '<<mask<<endl;return 2;}
 }
 cout<<"n="<<n<<" trianglefree_labeled="<<tf<<" connected="<<connected<<" non_complete_bipartite="<<noncb<<" minimum_D_minus_n_plus_2="<<(noncb?minslack:0)<<" maximum_sigma="<<maxsigma<<" bipartite_max="<<B<<endl;
 }
 for(long long n=7;n<=10000;n++){
  long long a=1;while(8*a*(n-a)<n*n)a++;
  long long d1=8*a*(n-a)-n*n,d2=n*n-8*(a-1)*(n-a+1);
  long long d=min(d1,d2);
  if(d*d>16*(n-3)*(n-3)){cerr<<"ROUND FAILURE "<<n;return 3;}
 }
 cout<<"Integer bracketing inequality verified n=7..10000 (diagnostic only)."<<endl;
}
