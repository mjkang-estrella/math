#include <bits/stdc++.h>
using namespace std;
int n,m; vector<pair<int,int>> E; vector<int>adj;
int cn(int a){return __builtin_popcount((unsigned)a);}
bool clique(int s){for(int v=0;v<n;v++)if(s>>v&1)if((adj[v]&s)!=(s^(1<<v)))return false;return true;}
int main(int argc,char**argv){
 ifstream f(argv[1]); string mode=argv[2]; int graphs=0,checks=0,defects=0; map<int,int>cnt;
 while(f>>n>>m){
 E.resize(m);adj.assign(n,0);for(auto &[a,b]:E){f>>a>>b;adj[a]|=1<<b;adj[b]|=1<<a;}
 if(n<3)continue;
 if(mode=="isolation"){
  for(int k=3;k<=min(n,5);k++){
   if(n==k && m==n*(n-1)/2)continue;
   vector<int>req;
   for(int s=1;s<(1<<n);s++)if(cn(s)==k&&clique(s)){
    int t=s;for(int v=0;v<n;v++)if(s>>v&1)t|=adj[v];req.push_back(t);
   }
   // Empty classes permitted, as in the source coloring equivalence.
   vector<int>c(n,-1);
   function<bool(int,int)> rec=[&](int v,int hi){
    if(v==n)return true;
    for(int x=0;x<=min(k,hi+1);x++){
     c[v]=x;bool ok=true;
     for(int t:req)if((t>>(v+1))==0){int cols=0;for(int z=0;z<=v;z++)if(t>>z&1)cols|=1<<c[z];if(cols!=(1<<(k+1))-1){ok=false;break;}}
     if(ok&&rec(v+1,max(x,hi)))return true;
    }c[v]=-1;return false;
   };
   bool ok=rec(0,-1);checks++;if(!ok){cout<<"DEFECT "<<n<<" "<<m<<" k "<<k<<endl;defects++;}
  }
 }else if(mode=="cycle"){
  vector<int>cycles;
  function<void(int,int,int)> dfs=[&](int root,int v,int s){
   if(cn(s)>=3&&(adj[v]>>root&1))cycles.push_back(s);
   for(int w=root+1;w<n;w++)if(!(s>>w&1)&&(adj[v]>>w&1))dfs(root,w,s|1<<w);
  };
  for(int v=0;v<n;v++)dfs(v,v,1<<v);
  for(int t=3;t<=n;t++){
   long double sum=0;
   for(int s=1;s<(1<<n);s++)if(cn(s)==t&&clique(s)){
    int gam=0;for(int cyc:cycles)if((s&cyc)==s)gam=max(gam,cn(cyc));
    long long bin=1;for(int j=1;j<=t;j++)bin=bin*(gam-j+1)/j;
    if(!bin){cout<<"undefined t "<<t<<endl;return 2;}
    sum+=(long double)(gam*(gam-1)/2)/bin;
   }
   checks++;if(sum>m+1e-8){defects++;cout<<"DEFECT n "<<n<<" m "<<m<<" t "<<t<<" sum "<<(double)sum<<endl;}
  }
 }
 graphs++;cnt[n]++;
 }
 cout<<mode<<" graphs "<<graphs<<" checks "<<checks<<" defects "<<defects<<endl;
 for(auto [a,b]:cnt)cout<<a<<" "<<b<<endl;
}
