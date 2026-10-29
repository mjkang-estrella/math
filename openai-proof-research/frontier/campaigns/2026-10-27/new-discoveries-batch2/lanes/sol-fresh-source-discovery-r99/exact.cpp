#include <bits/stdc++.h>
using namespace std;using U=uint64_t;
struct G{int n;vector<U>a;int gam;};
bool super(const vector<U>&a,U o){U covered=0;for(int v=0;v<(int)a.size();v++)if(!(o>>v&1)){U t=a[v]&o;if(t&&!(t&(t-1)))covered|=t;}return covered==o;}
int main(){vector<G> gs;for(int n=2;n<=5;n++){int e=n*(n-1)/2;set<U> seen;for(U m=0;m<(1ULL<<e);m++){vector<U>a(n);int z=0;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++,z++)if(m>>z&1){a[i]|=1ULL<<j;a[j]|=1ULL<<i;}U reach=1,last=0;while(reach!=last){last=reach;for(int i=0;i<n;i++)if(reach>>i&1)reach|=a[i];}if(reach!=(1ULL<<n)-1)continue;vector<int> p(n);iota(p.begin(),p.end(),0);U canon=~0ULL;do{U c=0;int k=0;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++,k++)if(a[p[i]]>>p[j]&1)c|=1ULL<<k;canon=min(canon,c);}while(next_permutation(p.begin(),p.end()));if(!seen.insert(canon).second)continue;int saving=0;for(U o=0;o<(1ULL<<n);o++)if(super(a,o))saving=max(saving,__builtin_popcountll(o));gs.push_back({n,a,n-saving});}}
cout<<"{\"factors\":[";for(int i=0;i<(int)gs.size();i++){if(i)cout<<',';cout<<"{\"n\":"<<gs[i].n<<",\"gamma\":"<<gs[i].gam<<",\"adj\":[";for(int j=0;j<gs[i].n;j++){if(j)cout<<',';cout<<gs[i].a[j];}cout<<"]}";}cout<<"],\"pairs\":[";bool first=true;for(int i=0;i<(int)gs.size();i++)for(int j=i;j<(int)gs.size();j++){G g=gs[i],h=gs[j];int n=g.n*h.n,rhs=g.gam*h.gam;if(rhs<=(n+1)/2)continue;vector<U>a(n);for(int x=0;x<g.n;x++)for(int y=0;y<h.n;y++){int v=x*h.n+y;for(int t=0;t<g.n;t++)if(g.a[x]>>t&1)a[v]|=1ULL<<(t*h.n+y);for(int t=0;t<h.n;t++)if(h.a[y]>>t&1)a[v]|=1ULL<<(x*h.n+t);}
U witness=0;int saving=0;for(U o=0;o<(1ULL<<n);o++){int k=__builtin_popcountll(o);if(k>n/2||k<=saving)continue;if(super(a,o)){saving=k;witness=o;}}
if(!first)cout<<',';first=false;cout<<"{\"i\":"<<i<<",\"j\":"<<j<<",\"order\":"<<n<<",\"rhs\":"<<rhs<<",\"gamma_product\":"<<n-saving<<",\"outside\":"<<witness<<"}"<<flush;}
cout<<"]}\n";
}
