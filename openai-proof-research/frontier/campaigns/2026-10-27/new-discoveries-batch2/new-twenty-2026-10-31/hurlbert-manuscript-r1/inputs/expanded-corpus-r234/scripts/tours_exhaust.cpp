#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <vector>
using namespace std;
vector<array<int,4>> ps; int fromv[24],tov[24],tour[24]; vector<int> outs[6]; long long checked=0,bad=0; bool capped=false;
int rank3(array<int,3> a){auto b=a;sort(b.begin(),b.end());for(int &x:a)x=find(b.begin(),b.end(),x)-b.begin();array<int,3> z={0,1,2};int k=0;do{if(z==a)return k;k++;}while(next_permutation(z.begin(),z.end()));return -1;}
bool good(){uint32_t adj[24]={};int deg[24]={};for(int i=0;i<24;i++)for(int a=0;a<4;a++)for(int b=0;b<4;b++)if(ps[tour[i]][a]<ps[tour[i]][b])adj[(i+a)%24]|=1u<<((i+b)%24);for(int i=0;i<24;i++)for(int j=0;j<24;j++)if(adj[i]>>j&1)deg[j]++;int q[24],lo=0,hi=0;for(int i=0;i<24;i++)if(!deg[i])q[hi++]=i;while(lo<hi){int i=q[lo++];for(int j=0;j<24;j++)if(adj[i]>>j&1)if(!--deg[j])q[hi++]=j;}return hi==24;}
void dfs(int k,int v,uint32_t used){if(capped)return;if(k==24){if(v!=fromv[0])return;checked++;if(!good()){bad++;if(bad==1){printf("first_bad:");for(int i:tour)printf(" %d",i);printf("\n");}}if(checked==2000000)capped=true;return;}for(int e:outs[v])if(!(used>>e&1)){tour[k]=e;dfs(k+1,tov[e],used|1u<<e);}}
int main(){array<int,4>a={0,1,2,3};do{ps.push_back(a);}while(next_permutation(a.begin(),a.end()));for(int i=0;i<24;i++){auto p=ps[i];fromv[i]=rank3({p[0],p[1],p[2]});tov[i]=rank3({p[1],p[2],p[3]});outs[fromv[i]].push_back(i);}tour[0]=0;dfs(1,tov[0],1);printf("n=4 fixed_first=1234 completed=%lld nonrealizable=%lld capped=%s\n",checked,bad,capped?"true":"false");}
