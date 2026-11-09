#include <bits/stdc++.h>
using namespace std;
int main(){for(int r=3;r<=4;r++)for(int n=r;n<=6;n++){vector<int>E;for(int x=0;x<(1<<n);x++)if(__builtin_popcount((unsigned)x)==r)E.push_back(x);int m=E.size();if(m>20)continue;vector<vector<unsigned>> need(1<<n,vector<unsigned>(n));for(int D=0;D<(1<<n);D++)for(int v=0;v<n;v++)if(!(D>>v&1))for(int j=0;j<m;j++)if((E[j]&(1<<v))&&((E[j]&~(1<<v))&D)==(E[j]&~(1<<v)))need[D][v]|=1u<<j;
 vector<int> best(n+1,-1);vector<unsigned>wit(n+1);for(unsigned h=0;h<(1u<<m);h++){int gamma=n;for(int D=0;D<(1<<n);D++)if(__builtin_popcount((unsigned)D)<gamma){bool ok=1;for(int v=0;v<n;v++)if(!(D>>v&1)&&!(need[D][v]&h)){ok=0;break;}if(ok)gamma=__builtin_popcount((unsigned)D);}int phi=n-gamma,k=__builtin_popcount(h);if(k>best[phi])best[phi]=k,wit[phi]=h;}
 cout<<"r "<<r<<" n "<<n<<" hypergraphs "<<(1u<<m)<<" max_edges_by_exact_phi ";for(int s=0;s<=n;s++)cout<<s<<":"<<best[s]<<",";cout<<endl;}}
