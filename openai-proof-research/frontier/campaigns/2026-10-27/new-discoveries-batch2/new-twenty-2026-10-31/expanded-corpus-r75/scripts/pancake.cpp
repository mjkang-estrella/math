#include <algorithm>
#include <array>
#include <iostream>
#include <vector>
using namespace std;
int main(){vector<array<int,4>> p;array<int,4>a={1,2,3,4};do{p.push_back(a);}while(next_permutation(a.begin(),a.end()));int nb[24][3];for(int v=0;v<24;v++)for(int k=0;k<3;k++){a=p[v];reverse(a.begin(),a.begin()+k+2);nb[v][k]=find(p.begin(),p.end(),a)-p.begin();}int best=0;unsigned witness=0;long hist[15]={};for(unsigned m=0;m<(1u<<23);m++){bool seen[72]={};int f=0;for(int d=0;d<72;d++)if(!seen[d]){f++;int x=d;do{seen[x]=true;int v=nb[x/3][x%3],k=x%3;int k2=(k+((m>>v)&1?2:1))%3;x=v*3+k2;}while(!seen[x]);}hist[f]++;if(f>best){best=f;witness=m;cout<<"improvement faces "<<best<<" genus "<<(14-best)/2<<" mask "<<m<<endl;}}cout<<"rotation systems modulo global reversal "<<(1u<<23)<<" maxfaces "<<best<<" witness "<<witness<<endl;for(int i=0;i<15;i++)if(hist[i])cout<<i<<" "<<hist[i]<<endl;}
