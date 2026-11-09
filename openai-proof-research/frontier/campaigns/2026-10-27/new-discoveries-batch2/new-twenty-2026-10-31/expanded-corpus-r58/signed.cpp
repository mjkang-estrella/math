#include <bits/stdc++.h>
using namespace std;
// Positive edges form H. A paired absolute-color block must induce a complete bipartite H.
string signature(int n,vector<int> adj){
 int M=1<<n,W=(n+1)*(n+1); vector<int> typ(M,-1); vector<vector<long long>> dp(M,vector<long long>(W)); dp[0][0]=1;
 for(int m=1;m<M;m++){
  int v=__builtin_ctz(m), B=adj[v]&m, A=m^B; bool ok=true;
  for(int i=0;i<n;i++) if(m>>i&1) if((adj[i]&m)!=((A>>i&1)?B:A))ok=false;
  if(ok)typ[m]=(B?1:0);
  int r=m^(1<<v);
  for(int t=r;;t=(t-1)&r){int b=t|(1<<v); if(typ[b]>=0){int s=m^b, da=typ[b],db=1-da;for(int a=0;a<=n;a++)for(int c=0;c+a<=n;c++)if(a+da+c+db<=n)dp[m][(a+da)*(n+1)+c+db]+=dp[s][a*(n+1)+c];}if(!t)break;}
 }
 ostringstream z;for(auto a:dp[M-1])z<<a<<',';
 // Sum of vertex-deleted histograms certifies equality of odd-color counts as well.
 for(int a=0;a<=n;a++)for(int b=0;b+a<=n;b++){long long s=0;for(int v=0;v<n;v++)s+=dp[(M-1)^(1<<v)][a*(n+1)+b]; z<<s<<',';}
 return z.str();
}
int main(){mt19937_64 rng(58);map<string,uint64_t> seen; int n=9;for(int trial=0;trial<2400;trial++){
 vector<int> adj(n); uint64_t mask=0;int p=0;
 for(int i=0;i<n;i++)for(int j=i+1;j<n;j++,p++){bool edge=(rng()%100)<(trial%3==0?25:trial%3==1?50:75);if(edge){mask|=1ULL<<p;adj[i]|=1<<j;adj[j]|=1<<i;}}
 string s=signature(n,adj);auto it=seen.find(s);if(it!=seen.end()&&it->second!=mask)cout<<"collision "<<n<<' '<<it->second<<' '<<mask<<endl;else seen[s]=mask;
 if(trial%200==0)cout<<"progress "<<trial<<" signatures "<<seen.size()<<endl;
 }cout<<"complete 2400 seeded n9 graphs; histogram collisions require independent isomorphism test"<<endl;}
