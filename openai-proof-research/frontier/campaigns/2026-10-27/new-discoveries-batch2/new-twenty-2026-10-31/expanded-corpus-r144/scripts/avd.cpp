#include <bits/stdc++.h>
using namespace std;
using ll=long long;
mt19937 rng(144);
pair<bool,bool> check(vector<int> a, bool report=false){
 int n=a.size(),N=1<<n,all=N-1;
 vector<int> cover(N); vector<ll> vc(n),vs(n);ll c=0,s=0;
 ll ec[20][20]={},es[20][20]={};
 for(int t=1;t<N;t++){int b=__builtin_ctz(t);cover[t]=cover[t^(1<<b)]|a[b]|(1<<b);}
 for(int t=0;t<N;t++){
  int miss=all^cover[t],k=__builtin_popcount((unsigned)t);
  if(!miss){
   c++;s+=k;
   int out=all^t;
   for(int v=0;v<n;v++)if(out>>v&1){vc[v]++;vs[v]+=k;
     int z=a[v]&t;if(z && !(z&(z-1))){int u=__builtin_ctz(z);ec[u][v]++;es[u][v]+=k;}
   }
  }else if(!(miss&(miss-1))){int v=__builtin_ctz(miss);vc[v]++;vs[v]+=k;}
 }
 bool vertex=false,edge=false;
 for(int v=0;v<n;v++)if(vs[v]*c<s*vc[v])vertex=true;
 for(int u=0;u<n;u++)for(int v=u+1;v<n;v++)if(a[u]>>v&1){
 ll lost=ec[u][v]+ec[v][u],weight=es[u][v]+es[v][u];
 if(s*lost>weight*c)edge=true;
 }
 if(report||!vertex||!edge){cout<<"n "<<n<<" avd "<<s<<"/"<<c<<" vertex "<<vertex<<" edge "<<edge<<" adjacency";for(int x:a)cout<<" "<<x;cout<<endl;}
 return {vertex,edge};
}
int main(int argc,char**argv){
 int n=atoi(argv[1]),count=atoi(argv[2]); double p=atof(argv[3]);int bad=0;
 for(int it=0;it<count;it++){
 vector<int>a(n);
 for(int u=0;u<n;u++)for(int v=u+1;v<n;v++)if(generate_canonical<double,20>(rng)<p){a[u]|=1<<v;a[v]|=1<<u;}
 if(accumulate(a.begin(),a.end(),0)==0)continue;
 auto [v,e]=check(a);if(!v||!e)bad++;
 }
 cout<<"completed "<<count<<" n "<<n<<" p "<<p<<" bad "<<bad<<endl;
}
