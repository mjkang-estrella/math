#include <algorithm>
#include <fstream>
#include <iostream>
#include <vector>
#include <queue>
#include <sys/resource.h>
#include <unistd.h>
using namespace std;
int main(int argc,char**argv){rlimit mem{536870912,536870912},cpu{160,165};setrlimit(RLIMIT_AS,&mem);setrlimit(RLIMIT_CPU,&cpu);alarm(175);string path=argv[1];ofstream report(path+"/steiner-report.tsv");report<<"a\tb\te\tvertices\tgroups\tentries\tlower_bound\n";
 for(int a=1;a<=10;a++)for(int b=1;b<=a;b++)for(int e=0;e<2;e++){
 // A reflection interchanges parity when either span is odd.
 if(e && (a%2||b%2))continue;
 vector<pair<int,int>> V,S;for(int u=0;u<=a;u++)for(int v=e;v<=e+b;v++)if((u-v)%2==0)V.push_back({u,v});
 for(int u=a-5;u<=5;u++)for(int v=e+b-5;v<=e+5;v++)if((u-v)%2==0)S.push_back({u,v});
 int n=V.size();vector<unsigned long long> C;
 for(auto [u,v]:S){unsigned long long c=0;for(int i=0;i<n;i++){auto [x,y]=V[i];if((abs(x-u)==4&&y==v)||(x==u&&abs(y-v)==4))c|=1ULL<<i;}C.push_back(c);}
 for(int side=0;side<4;side++){unsigned long long c=0;for(int i=0;i<n;i++){auto [u,v]=V[i];if((side==0&&u==0)||(side==1&&u==a)||(side==2&&v==e)||(side==3&&v==e+b))c|=1ULL<<i;}C.push_back(c);}
 sort(C.begin(),C.end());C.erase(unique(C.begin(),C.end()),C.end());vector<unsigned long long> G;
 for(auto c:C){bool redundant=false;for(auto d:C)if(d!=c&&(d&c)==d)redundant=true;if(!redundant)G.push_back(c);}
 if(G[0]==0){report<<a<<'\t'<<b<<'\t'<<e<<'\t'<<n<<"\t0\t0\t12\n";continue;}
 int k=G.size(),N=1<<k;vector<vector<int>>adj(n);vector<int> cover(n);
 for(int i=0;i<n;i++){for(int j=0;j<n;j++)if(abs(V[i].first-V[j].first)==1&&abs(V[i].second-V[j].second)==1)adj[i].push_back(j);for(int g=0;g<k;g++)if(G[g]>>i&1)cover[i]|=1<<g;}
 vector<unsigned char> dp((size_t)N*n,12);
 for(int v=0;v<n;v++){for(int m=cover[v];m;m=(m-1)&cover[v])dp[(size_t)m*n+v]=1;}
 for(int m=1;m<N;m++){
 auto D=&dp[(size_t)m*n];for(int s=(m-1)&m;s;s=(s-1)&m){int t=m^s;if(s>t)continue;auto A=&dp[(size_t)s*n];auto B=&dp[(size_t)t*n];for(int v=0;v<n;v++)D[v]=min<int>(D[v],A[v]+B[v]-1);}
 // Exact shortest-path closure with unit edges, capped at 12.
 for(int cost=1;cost<11;cost++)for(int v=0;v<n;v++)if(D[v]==cost)for(int w:adj[v])D[w]=min<int>(D[w],cost+1);
 }
 int lower=*min_element(dp.end()-n,dp.end());report<<a<<'\t'<<b<<'\t'<<e<<'\t'<<n<<'\t'<<k<<'\t'<<dp.size()<<'\t'<<lower<<endl;
 string name=path+"/steiner-"+to_string(a)+"-"+to_string(b)+"-"+to_string(e)+".bin";ofstream out(name,ios::binary);out.write((char*)dp.data(),dp.size());if(lower<12){cerr<<"FAILED "<<a<<' '<<b<<' '<<e<<' '<<lower<<endl;return 2;}
 }
}
