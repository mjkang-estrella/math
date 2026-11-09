#include <bits/stdc++.h>
using namespace std;
int N; bool st; int d[24],a[24][24]; unsigned long long total,valid,best;vector<pair<int,int>> be;
bool connected(int rem){int s=rem==0?1:0;int mask=1<<s;vector<int>q={s};for(int i=0;i<(int)q.size();i++)for(int j=0;j<N;j++)if(j!=rem&&a[q[i]][j]&&!(mask>>j&1))mask|=1<<j,q.push_back(j);return q.size()==N-1;}
void rec(){
 int u=0;while(u<N&&!d[u])u++;
 if(u==N){total++;long long p[24]={1};for(int j=1;j<N;j++)for(int i=0;i<j;i++)if(a[i][j])p[j]+=p[i];
 if((unsigned long long)p[N-1]<=best)return;
 if(!st)for(int r=0;r<N;r++)if(!connected(r))return;
 valid++;best=p[N-1];be.clear();for(int i=0;i<N;i++)for(int j=i+1;j<N;j++)if(a[i][j])be.emplace_back(i,j);
 return;}
 // Force the least remaining vertex, with increasing partners when it has two stubs.
 if(d[u]==2){for(int v=u+2;v<N;v++)if(d[v]&&!a[u][v])for(int w=v+1;w<N;w++)if(d[w]&&!a[u][w]){
 d[u]-=2;d[v]--;d[w]--;a[u][v]=a[v][u]=a[u][w]=a[w][u]=1;
 rec();a[u][v]=a[v][u]=a[u][w]=a[w][u]=0;d[u]+=2;d[v]++;d[w]++;}}
 else for(int v=u+2;v<N;v++)if(d[v]&&!a[u][v]){d[u]--;d[v]--;a[u][v]=a[v][u]=1;rec();a[u][v]=a[v][u]=0;d[u]++;d[v]++;}
}
int main(int argc,char**argv){int upto=atoi(argv[1]);st=atoi(argv[2]);for(N=4;N<=upto;N+=2){memset(a,0,sizeof(a));fill(d,d+N,1);for(int i=0;i<N-1;i++)a[i][i+1]=a[i+1][i]=1;if(st)a[0][N-1]=a[N-1][0]=1;else d[0]=d[N-1]=2;total=valid=best=0;rec();long long pow3=1;for(int i=0;i<N/2;i++)pow3*=3;cout<<"N "<<N<<" fixed_st "<<st<<" completions "<<total<<" maximum "<<best<<" bound_squared "<<pow3<<" violation "<<((best-1)*(best-1)>pow3)<<" edges";for(auto [u,v]:be)cout<<" "<<u<<","<<v;cout<<endl;}}
