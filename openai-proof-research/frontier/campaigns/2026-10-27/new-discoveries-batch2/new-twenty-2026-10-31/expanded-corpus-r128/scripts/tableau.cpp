#include <array>
#include <map>
#include <iostream>
#include <cstdint>
using A=std::array<int,4>; using U=uint64_t;
int n,b[9],shape[3]; U total; std::map<A,U> counts;
void dfs(int prev,int left){
 if(!left){counts[{b[0],b[1],b[3],b[4]}]++;total++;return;}
 for(int r=0;r<3;r++)if(shape[r]<n&&(!r||shape[r]<shape[r-1])){
 shape[r]++;if(prev>=0)b[3*prev+r]++;dfs(r,left-1);if(prev>=0)b[3*prev+r]--;shape[r]--;}
}
int main(int argc,char**argv){int cap=argc>1?atoi(argv[1]):8;for(n=1;n<=cap;n++){
 counts.clear();total=0;dfs(-1,3*n);bool alpha=true,delta=true;std::map<std::array<int,3>,U> dc;
 for(auto [a,c]:counts)dc[{a[1],a[3],a[4]}]+=c;
 for(auto [a,c]:counts){int x=a[0],y=a[1],z=a[2],w=a[3]; A aa={z,n-z-w,x,n-x-y};if(counts.find(aa)==counts.end()||counts.at(aa)!=c){alpha=false;std::cout<<"alpha failure "<<x<<","<<y<<","<<z<<","<<w<<" count "<<c<<"\n";break;}}
 for(auto [a,c]:dc){auto [y,z,w]=a;std::array<int,3> aa={y,n-z-w-1,w};if(dc.find(aa)==dc.end()||dc.at(aa)!=c){delta=false;break;}}
 std::cout<<"n "<<n<<" tableaux "<<total<<" signatures "<<counts.size()<<" alpha "<<alpha<<" delta "<<delta<<std::endl;
}}
