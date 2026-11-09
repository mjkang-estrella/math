#include <algorithm>
#include <iostream>
#include <vector>
using namespace std;
int main(){ const int N=160;
 for(int k=1;k<=65;k+=4){int Y=2*N/k+1;vector<unsigned char> p((N+1)*(N+1)*Y);auto at=[&](int x,int y,int z)->unsigned char&{return p[(x*(N+1)+z)*Y+y];};long long states=0,bad=0,interior=0;int fx=-1,fy=-1,fz=-1;
 for(int x=0;x<=N;x++)for(int z=0;z<=N;z++)for(int y=0;y<Y&&y<=(x+z)/k;y++){
 bool lose=true;for(int u=0;u<x&&lose;u++)if(at(u,min(y,(u+z)/k),z))lose=false;
 for(int v=0;v<y&&lose;v++)if(at(x,v,z))lose=false;
 for(int w=0;w<z&&lose;w++)if(at(x,min(y,(x+w)/k),w))lose=false;
 at(x,y,z)=lose;states++;bool pred=(((x-1)^y^(z-1))==0);
 if(pred!=lose){bad++;if(x&&z){interior++;if(fx<0){fx=x;fy=y;fz=z;}}}
 }
 cout<<"k="<<k<<" N="<<N<<" states="<<states<<" mismatches="<<bad<<" positive_xz_mismatches="<<interior<<" first="<<fx<<","<<fy<<","<<fz<<endl;
 }
}
