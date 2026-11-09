#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <iostream>
#include <numeric>
#include <random>
using namespace std;
int main(){
 mt19937 rng(365453); array<int,30>a,u,v; array<int,16>w{},g;
 for(int t=0;t<6;t++){
 int h=t/3, l=2*t,r=l+1,x=12+2*h,y=x+1;
 int us[]={l,l,l,r,r},vs[]={r,x,y,x,y};
 for(int j=0;j<5;j++)u[5*t+j]=us[j],v[5*t+j]=vs[j];
 g[l]=0;g[r]=1;
 }g[12]=g[13]=2;g[14]=g[15]=3;
 auto score=[&](){long s[4]={},sq[4]={},n[4]={};for(int i=0;i<16;i++){s[g[i]]+=w[i];sq[g[i]]+=w[i]*w[i];n[g[i]]++;}long z=0;for(int j=0;j<4;j++)z+=n[j]*sq[j]-s[j]*s[j];return z;};
 auto start=chrono::steady_clock::now(); int best=1000000000;long iterations=0;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<18){
 iota(a.begin(),a.end(),1);shuffle(a.begin(),a.end(),rng);w.fill(0);
 for(int j=0;j<30;j++)w[u[j]]+=a[j],w[v[j]]+=a[j];
 long cur=score();
 for(int k=0;k<200000;k++,iterations++){
 int i=rng()%30,j=rng()%30;int d=a[j]-a[i];
 w[u[i]]+=d;w[v[i]]+=d;w[u[j]]-=d;w[v[j]]-=d;
 long next=score();double temp=0.2+45.0*(1.0-double(k)/200000);
 if(next<=cur || double(rng())/rng.max()<exp(double(cur-next)/temp)){swap(a[i],a[j]);cur=next;}
 else {w[u[i]]-=d;w[v[i]]-=d;w[u[j]]+=d;w[v[j]]+=d;}
 best=min(best,int(cur));
 if(cur==0){
 bool proper=true;for(int e=0;e<30;e++)if(w[u[e]]==w[v[e]])proper=false;
 if(proper){cout<<"FOUND\n";for(int z:a)cout<<z<<" ";cout<<"\n";for(int z:w)cout<<z<<" ";cout<<"\n";return 0;}
 }
 }
 }cout<<"NOT FOUND best "<<best<<" iterations "<<iterations<<"\n";
}
