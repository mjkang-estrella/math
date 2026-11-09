#include <algorithm>
#include <array>
#include <bitset>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
int P,N,T; vector<int> facets,sel; unsigned long long tested=0,matched=0,disconnected=0; int parent[500];
int root(int x){return parent[x]==x?x:parent[x]=root(parent[x]);}
bool unite(int a,int b){a=root(a);b=root(b);if(a==b)return false;parent[a]=b;return true;}
void check(){
 tested++;int vertices=0;bitset<256> faces[5];
 for(int f:sel){vertices|=f; for(int x=f;x;x=(x-1)&f) faces[__builtin_popcount((unsigned)x)-1].set(x);}
 if(__builtin_popcount((unsigned)vertices)!=P)return;
 bool count=false;for(int k=1;k<N;k++){
  int c=1,d=1;for(int j=1;j<=k;j++){c=c*(N-j+1)/j;d=d*(N-j)/(j);}
  // C(N,k+1) independently
  d=1;for(int j=1;j<=k+1;j++)d=d*(N-j+1)/j;
  if((int)faces[k].count()==T*c+d)count=true;
 }
 if(!count)return;matched++;
 // absence of (N-1,N) circuits is forest in facet-ridge incidence bipartite graph
 iota(parent,parent+500,0);int ridgemap[256];fill(ridgemap,ridgemap+256,-1);int next=T;bool cyclic=false;
 for(int i=0;i<T;i++)for(int v=0;v<P;v++)if(sel[i]>>v&1){int r=sel[i]^(1<<v);if(ridgemap[r]<0)ridgemap[r]=next++;if(!unite(i,ridgemap[r]))cyclic=true;}
 if(cyclic)return;
 bool connected=true;for(int i=1;i<T;i++)if(root(i)!=root(0))connected=false;
 if(!connected){disconnected++;cout<<"COUNTEREXAMPLE n="<<N<<" p="<<P<<" facets";for(int f:sel)cout<<" "<<f;cout<<"\n";}
}
void rec(int at){if((int)sel.size()==T){check();return;}for(int i=at;i<=(int)facets.size()-(T-(int)sel.size());i++){sel.push_back(facets[i]);rec(i+1);sel.pop_back();}}
int main(int argc,char**argv){N=atoi(argv[1]);P=atoi(argv[2]);T=P-N;for(int f=1;f<(1<<P);f++)if(__builtin_popcount((unsigned)f)==N+1)facets.push_back(f);rec(0);cout<<"n="<<N<<" p="<<P<<" tested="<<tested<<" face_count_matched="<<matched<<" circuit_free_disconnected="<<disconnected<<"\n";}
