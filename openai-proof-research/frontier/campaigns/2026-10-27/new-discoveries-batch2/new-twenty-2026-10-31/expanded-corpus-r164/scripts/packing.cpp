#include <bits/stdc++.h>
using namespace std;
mt19937 rng(1642026);long long nodes;const int CAP=3000000;
struct Solver {int n,m,k,weak;vector<pair<int,int>> E;vector<unsigned> dom;vector<vector<int>> conflict[2];vector<int>ans;
bool go(vector<unsigned> d,vector<int> c,int left){if(++nodes>CAP)return false;if(!left){ans=c;return true;}int e=-1,z=99;for(int i=0;i<m;i++)if(c[i]<0){int t=__builtin_popcount(d[i]);if(!t)return false;if(t<z)z=t,e=i;}unsigned tried=0;for(int a=0;a<k;a++)if(d[e]>>a&1){ // unused symmetric colors of each radius need one representative
 bool used=false;for(int x:c)if(x==a)used=true;
 unsigned bit=1u<<(a<weak?0:1);if(!used && (tried&bit))continue;if(!used)tried|=bit;
 auto dd=d;auto cc=c;cc[e]=a;bool ok=true;for(int f:conflict[a<weak?0:1][e])if(cc[f]<0){dd[f]&=~(1u<<a);if(!dd[f]){ok=false;break;}}else if(cc[f]==a){ok=false;break;}
 if(ok&&go(dd,cc,left-1))return true;}return false;}
bool solve(vector<pair<int,int>> es,int nn,int kk,int ww){E=es;n=nn;m=E.size();k=kk;weak=ww;for(int t=0;t<2;t++)conflict[t].assign(m,{});vector<vector<int>>adj(n,vector<int>(n));for(auto[u,v]:E)adj[u][v]=adj[v][u]=1;
 for(int i=0;i<m;i++)for(int j=0;j<m;j++)if(i!=j){auto[u,v]=E[i];auto[x,y]=E[j];bool near=u==x||u==y||v==x||v==y;if(near)conflict[0][i].push_back(j);if(near||adj[u][x]||adj[u][y]||adj[v][x]||adj[v][y])conflict[1][i].push_back(j);}
 nodes=0;return go(vector<unsigned>(m,(1u<<k)-1),vector<int>(m,-1),m);}
bool verify(){for(int i=0;i<m;i++)for(int j:conflict[ans[i]<weak?0:1][i])if(ans[i]==ans[j])return false;return true;}};
int main(int argc,char**argv){int per=argc>1?atoi(argv[1]):100;Solver s;int cnt=0,unknown=0;for(int n=4;n<=40;n+=2)for(int type=0;type<2;type++)for(int it=0;it<per;it++){
 vector<pair<int,int>>E;bool good=false;for(int attempt=0;attempt<10000&&!good;attempt++){E.clear();set<pair<int,int>>ed;vector<int>v; if(type==0){for(int t=0;t<3;t++){v.resize(n);iota(v.begin(),v.end(),0);shuffle(v.begin(),v.end(),rng);for(int i=0;i<n;i+=2)ed.insert(minmax(v[i],v[i+1]));}}else{for(int i=0;i<n;i++)for(int j=0;j<3;j++)v.push_back(i);shuffle(v.begin(),v.end(),rng);for(int i=0;i<3*n;i+=2)if(v[i]!=v[i+1])ed.insert(minmax(v[i],v[i+1]));}if((int)ed.size()!=3*n/2)continue;E.assign(ed.begin(),ed.end());good=true;}
 if(!good)continue;bool ok=s.solve(E,n,type==0?5:6,2);if(ok){if(!s.verify())abort();cnt++;}else {unknown++;cout<<"FAIL_OR_CAP n="<<n<<" type="<<type<<" nodes="<<nodes<<" edges=";for(auto[u,v]:E)cout<<u<<","<<v<<";";cout<<endl;}
 if(it==per-1)cout<<"n="<<n<<" type="<<type<<" cumulative_sat="<<cnt<<" unknown="<<unknown<<endl;
 }cout<<"FINAL "<<cnt<<" "<<unknown<<endl;}
