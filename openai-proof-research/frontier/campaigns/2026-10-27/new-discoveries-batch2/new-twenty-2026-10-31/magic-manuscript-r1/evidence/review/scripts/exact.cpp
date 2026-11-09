#include <algorithm>
#include <iostream>
#include <vector>
using namespace std;
long long nodes=0,solutions=0;int a[11],best=100;bool used[12];
void dfs(int d,int mask,int lo,int hi){
 ++nodes;
 if(d==7){int t=a[6]+a[0];if(mask&(1<<t))return; mask|=1<<t;lo=min(lo,t);hi=max(hi,t);int j=7;for(int v=1;v<=11;v++)if(!used[v]){a[j++]=v;t=a[0]+v;if(mask&(1<<t))return;mask|=1<<t;lo=min(lo,t);hi=max(hi,t);}if(hi-lo!=10)return;solutions++;if(lo<best){best=lo;cout<<"minimum_s "<<best<<" labels";for(int v:a)cout<<' '<<v;cout<<'\n';}return;}
 for(int v=1;v<=11;v++)if(!used[v]){int t=a[d-1]+v;if(mask&(1<<t))continue;int l=min(lo,t),h=max(hi,t);if(h-l>10)continue;a[d]=v;used[v]=true;dfs(d+1,mask|(1<<t),l,h);used[v]=false;}
}
int main(){for(int h=1;h<=11;h++){a[0]=h;used[h]=true;dfs(1,0,99,0);used[h]=false;}cout<<"nodes "<<nodes<<" solutions "<<solutions<<" exact_strength "<<22+best<<'\n';}
