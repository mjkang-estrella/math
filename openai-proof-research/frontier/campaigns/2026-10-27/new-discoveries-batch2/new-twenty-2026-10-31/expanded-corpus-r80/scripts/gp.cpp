#include <bits/stdc++.h>
using namespace std;
int gp(int n, vector<pair<int,int>>&e, unsigned mask){
 int d[12][12];for(int i=0;i<n;i++)for(int j=0;j<n;j++)d[i][j]=i==j?0:99;
 for(int k=0;k<(int)e.size();k++){auto [a,b]=e[k];if(mask>>k&1)swap(a,b);d[a][b]=1;}
 for(int k=0;k<n;k++)for(int i=0;i<n;i++)for(int j=0;j<n;j++)d[i][j]=min(d[i][j],d[i][k]+d[k][j]);
 vector<int> bad;
 for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int c=b+1;c<n;c++){
  int v[3]={a,b,c};bool no=0;do{if(d[v[0]][v[2]]<99&&d[v[0]][v[2]]==d[v[0]][v[1]]+d[v[1]][v[2]])no=1;}while(next_permutation(v,v+3));
  if(no)bad.push_back((1<<a)|(1<<b)|(1<<c));
 }
 int best=0;for(int s=0;s<(1<<n);s++){int pc=__builtin_popcount((unsigned)s);if(pc<=best)continue;bool ok=1;for(int t:bad)if((s&t)==t){ok=0;break;}if(ok)best=pc;}return best;
}
int main(){int id,n,m;long long orientations=0;while(cin>>id>>n>>m){vector<pair<int,int>>e(m);for(auto &[a,b]:e)cin>>a>>b;unsigned spectrum=0;for(unsigned s=0;s<(1u<<m);s++)spectrum|=1u<<gp(n,e,s);orientations+=1u<<m;int lo=__builtin_ctz(spectrum),hi=31-__builtin_clz(spectrum);bool ok=spectrum==((1u<<(hi+1))-(1u<<lo));cout<<id<<" "<<n<<" "<<m<<" "<<spectrum<<" "<<ok<<" cumulative_orientations "<<orientations<<endl;if(!ok)return 2;}}
