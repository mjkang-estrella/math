#include <bits/stdc++.h>
using namespace std;
int n;set<unsigned> rays;unsigned long long leaves,nodes;
void dfs(int r,unsigned cols,unsigned diag){nodes++;if(r==n){rays.insert(diag);leaves++;return;}for(int c=0;c<n;c++)if(!(cols>>c&1)&&!(diag>>(n-1+r-c)&1))dfs(r+1,cols|(1u<<c),diag|(1u<<(n-1+r-c)));}
unsigned long long scores(int n,int pos,int prev,int sum){if(pos==n)return sum==n*(n-1)/2;unsigned long long ans=0;for(int x=prev;x<n;x++)if(sum+x>=(pos+1)*pos/2 && sum+x+(n-pos-1)*(n-1)>=n*(n-1)/2 && sum+x<=n*(n-1)/2)ans+=scores(n,pos+1,x,sum+x);return ans;}
int main(){for(n=1;n<=12;n++){rays.clear();leaves=nodes=0;dfs(0,0,0);cout<<n<<" "<<rays.size()<<" "<<scores(n,0,0,0)<<" "<<leaves<<" "<<nodes<<endl;}}
