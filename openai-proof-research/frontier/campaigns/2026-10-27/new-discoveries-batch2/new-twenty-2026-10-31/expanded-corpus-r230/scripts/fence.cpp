#include <bits/stdc++.h>
using namespace std; using U=uint64_t;
vector<U> rankpoly(int n,int m,uint64_t mask){int z=n*m+1;vector<vector<U>>d(m+1,vector<U>(z));for(int x=0;x<=m;x++)d[x][x]=1;
for(int i=1;i<n;i++){vector<vector<U>> e(m+1,vector<U>(z));for(int x=0;x<=m;x++)for(int y=0;y<=m;y++)if(((mask>>(i-1))&1)?y<=x:y>=x)for(int s=0;s<=(i*m);s++)e[y][s+y]+=d[x][s];d.swap(e);}vector<U>a(z);for(auto&r:d)for(int s=0;s<z;s++)a[s]+=r[s];return a;}
int main(int argc,char**argv){int N=atoi(argv[1]),lo=atoi(argv[2]),hi=atoi(argv[3]);uint64_t count=0;for(int n=1;n<=N;n++){uint64_t done=0;for(uint64_t w=0;w<(1ULL<<max(0,n-1));w++){// fix initial sign by order duality
if(n>1 && (w&1))continue;
for(int m=lo;m<=hi;m++){auto a=rankpoly(n,m,w);bool down=false;for(int i=1;i<(int)a.size();i++){if(a[i]<a[i-1])down=true;if(down&&a[i]>a[i-1]){cout<<"COUNTEREXAMPLE "<<n<<" "<<m<<" "<<w<<" "<<i<<endl;for(auto x:a)cout<<x<<",";cout<<endl;return 1;}}count++;done++;}}cout<<"n="<<n<<" instances="<<done<<" cumulative="<<count<<" no dip"<<endl;}}
