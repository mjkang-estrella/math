#include <algorithm>
#include <array>
#include <chrono>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
int countAS(const vector<int>&w){set<vector<int>>s;int n=w.size();for(int i=0;i<n;i++)for(int h=1;i+2*h<=n;h++){array<int,32>c{};for(int j=0;j<h;j++)c[w[i+j]]++,c[w[i+j+h]]--;if(all_of(c.begin(),c.end(),[](int x){return x==0;}))s.emplace(w.begin()+i,w.begin()+i+2*h);}return s.size();}
int main(int argc,char**argv){string mode=argv[1];mt19937 rng(1501); auto start=chrono::steady_clock::now();
if(mode=="words"){
 for(int n=1;n<=10;n++){int best=0,quotientFailures=0;long long checked=0;vector<int>w(n),example;auto rec=[&](auto&&self,int p,int mx)->void{if(p==n){checked++;int v=countAS(w),qbest=0; if(mx<=1)best=max(best,v);for(int mask=0;mask<(1<<mx);mask++){vector<int>b;for(int c:w)b.push_back(c==0?0:((mask>>(c-1))&1));qbest=max(qbest,countAS(b));}if(qbest<v){quotientFailures++;if(example.empty())example=w;}return;}for(int c=0;c<=mx+1;c++){w[p]=c;self(self,p+1,max(mx,c));}};w[0]=0;rec(rec,1,0);cout<<"n "<<n<<" canonical_words "<<checked<<" binary_max "<<best<<" quotient_failures "<<quotientFailures<<" first ";for(int c:example)cout<<c;cout<<endl;}
}
if(mode=="chip"){
 for(int n:{11,13,15,17,21,25,31}){int steps=0,m=n/2;for(int i=1;i<=m;i++)steps+=i*i;int best=-1;vector<int>gene(steps);for(auto&x:gene)x=rng();
 auto run=[&](vector<int>const&g){map<int,vector<int>>p;for(int i=1;i<=n;i++)p[0].push_back(i);int t=0;while(true){vector<int>active;for(auto&[x,v]:p)if(v.size()>1)active.push_back(x);if(active.empty())break;unsigned z=g[t++];int x=active[z%active.size()];z=z/active.size();auto &v=p[x];int a=z%v.size();z/=v.size();int b=z%(v.size()-1);if(b>=a)b++;int lo=min(v[a],v[b]),hi=max(v[a],v[b]);if(a>b)swap(a,b);v.erase(v.begin()+b);v.erase(v.begin()+a);p[x-1].push_back(lo);p[x+1].push_back(hi);}vector<int>w;for(auto&[x,v]:p)for(int a:v)w.push_back(a);int inv=0;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)inv+=w[i]>w[j];return inv;};
 int score=run(gene);long long trials=0;auto local=chrono::steady_clock::now();while(chrono::duration<double>(chrono::steady_clock::now()-local).count()<7){vector<int>g=gene;int mut=1+rng()%max(2,steps/10);for(int i=0;i<mut;i++)g[rng()%steps]=rng();int v=run(g);trials++;if(v>=score||rng()%300==0)gene=g,score=v;if(v>best)best=v;if(v>m){cout<<"COUNTEREXAMPLE n "<<n<<" inv "<<v<<endl;return 0;}if(trials%1000==0){for(auto&x:gene)x=rng();score=run(gene);}}
 cout<<"n "<<n<<" move_count "<<steps<<" trials "<<trials<<" best_inversions "<<best<<" conjectured "<<m<<endl;}
}
if(mode=="fraction"){
 for(auto cfg:vector<array<int,4>>{{4,2,3,2},{5,2,3,2},{4,3,3,2},{4,2,3,3},{7,2,3,2},{5,2,4,2}}){auto[m,a,k,q]=cfg;vector<vector<int>>colors;vector<int>c(k);auto gen=[&](auto&&self,int j,int rem)->void{if(j==k-1){c[j]=rem;colors.push_back(c);return;}for(int x=0;x<=rem;x++){c[j]=x;self(self,j+1,rem-x);}};gen(gen,0,q);vector<vector<int>>parts;vector<int>part;auto gp=[&](auto&&self,int low)->void{if((int)part.size()==a){parts.push_back(part);return;}for(int i=low;i<(int)colors.size();i++){part.push_back(i);self(self,i);part.pop_back();}};gp(gp,0);int h=parts.size();vector<vector<vector<int>>>con(h,vector<vector<int>>(h,vector<int>(a)));for(int i=0;i<h;i++)for(int j=0;j<h;j++)for(int u=0;u<a;u++)for(int v=0;v<a;v++)for(int z=0;z<k;z++)con[i][j][u]+=min(colors[parts[i][u]][z],colors[parts[j][v]][z]);int best=100000,bound=((m+k-1)/k-1)*a*q;long long checked=0;vector<int>ps;auto rec=[&](auto&&self,int lo)->void{if((int)ps.size()==m){checked++;int d=0;for(int i=0;i<m;i++)for(int u=0;u<a;u++){int t=0;for(int j=0;j<m;j++)if(i!=j)t+=con[ps[i]][ps[j]][u];d=max(d,t);}best=min(best,d);return;}for(int i=lo;i<h;i++){ps.push_back(i);self(self,i);ps.pop_back();}};rec(rec,0);cout<<"m "<<m<<" a "<<a<<" k "<<k<<" denominator "<<q<<" part_types "<<h<<" configurations "<<checked<<" min_defect_numerator "<<best<<" conjectured_numerator "<<bound<<endl;}
}
cout<<"seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
}
