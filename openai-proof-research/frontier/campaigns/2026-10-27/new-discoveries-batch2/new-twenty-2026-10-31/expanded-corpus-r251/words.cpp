#include <iostream>
#include <vector>
#include <map>
#include <string>
using namespace std;
long long levels[26]={};
vector<vector<long long>> sig(2048,vector<long long>(17));
int pref[30]={};
void dfs(unsigned w,int n){
 levels[n]++;
 for(int k=1;k<=10&&k<n;k++){if(n-k<=16) sig[(1<<k)|(w>>(n-k))][n-k]++;}
 if(n==24)return;
 for(int b=0;b<2;b++){
  pref[n+1]=pref[n]+b; bool ok=true;
  for(int k=1;k<=n+1;k++) if(pref[n+1]-pref[n+1-k]>pref[k]){ok=false;break;}
  if(ok)dfs((w<<1)|b,n+1);
 }
}
int main(){pref[1]=1;dfs(1,1);
 for(int n=1;n<=24;n++)cout<<"level "<<n<<" "<<levels[n]<<"\n";
 map<vector<long long>,vector<int>> groups;
 for(int n=1;n<=8;n++)for(int w=0;w<(1<<n);w++)if(sig[(1<<n)|w][1])groups[sig[(1<<n)|w]].push_back((1<<n)|w);
 int collisions=0;
 for(auto &p:groups)if(p.second.size()>1){collisions++;cout<<"collision";for(int w:p.second){string s;while(w>1){s=char('0'+(w&1))+s;w>>=1;}cout<<" "<<s;}cout<<" counts";for(auto a:p.first)cout<<" "<<a;cout<<"\n";}
 cout<<"collision_groups_through_m16_prefix_lengths_le8 "<<collisions<<"\n";
}
