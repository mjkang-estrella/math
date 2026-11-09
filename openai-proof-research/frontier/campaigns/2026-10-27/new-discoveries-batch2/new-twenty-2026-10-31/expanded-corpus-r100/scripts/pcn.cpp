#include <bits/stdc++.h>
using namespace std;const int p=11,q=19487171,N=q-1; //11^7
int mul(int a,int b){int u[7],v[7],w[13]={};for(int i=0;i<7;i++){u[i]=a%11;a/=11;v[i]=b%11;b/=11;}for(int i=0;i<7;i++)for(int j=0;j<7;j++)w[i+j]+=u[i]*v[j];for(int i=12;i>=7;i--){int t=(w[i]%11+11)%11;w[i-7]-=4*t;w[i-6]-=t;}int z=0;for(int i=6;i>=0;i--)z=11*z+(w[i]%11+11)%11;return z;}
int pw(int a,int b){int r=1;for(;b;b/=2,a=mul(a,a))if(b&1)r=mul(r,a);return r;}
int add(int a,int b){int r=0,t=1;for(int i=0;i<7;i++,t*=11,a/=11,b/=11)r+=((a%11+b%11)%11)*t;return r;}
int main(){vector<int>f;int n=N;for(int z=2;z*z<=n;z++)if(n%z==0){f.push_back(z);while(n%z==0)n/=z;}if(n>1)f.push_back(n);int s=0;for(;s<11;s++){bool ok=true;for(int z:f)if(pw(11+s,N/z)==1)ok=false;if(ok)break;}cout<<"modulus X^7+X+4; primitive X+"<<s<<"\n";
vector<int> ex(N),lg(q,-1);int v=1;for(int i=0;i<N;i++){if(lg[v]>=0){cout<<"bad period "<<i;return 1;}ex[i]=v;lg[v]=i;int a[7];for(int j=0,w=v;j<7;j++,w/=11)a[j]=w%11;int top=a[6],z=0;for(int j=6;j>=0;j--){int c=s*a[j]+(j?a[j-1]:0)-(j==0?4*top:j==1?top:0);z=z*11+(c%11+11)%11;}v=z;}assert(v==1);cout<<"field elements enumerated "<<q<<"\n";
set<int> known;long long pp[8]={1};for(int j=1;j<=7;j++)pp[j]=pp[j-1]*11;vector<long long>b={1,(pp[2]+1)/2,10*pp[6]+pp[5]+9*pp[3]+10*pp[2]+11,(pp[4]+1)/2,(pp[6]+1)/2,9*pp[6]+9*pp[5]+10*pp[4]+pp[3]+pp[2]+11,(pp[7]+1)/12};for(auto z:b)for(int j=0;j<7;j++)known.insert(z*pp[j]%N);
vector<int> seen(q,0);mt19937 rng(346233);vector<int> xs;for(int i=0;i<50000;i++)xs.push_back(rng()%q);int count=0,fail=0;vector<int>surv;
for(int t=0;t<20000;t++){int d=t<10000?2*t+1:((rng()%(N/2))*2+1);if(known.count(d))continue;count++;if(gcd(d,N)!=1){fail++;continue;}bool collision=false;for(int x:xs){int xp=x-x%11+(x%11+1)%11;int a=x?ex[(long long)lg[x]*d%N]:0;int b=xp?ex[(long long)lg[xp]*d%N]:0;int y=add(a,b);if(seen[y]==count){collision=true;break;}seen[y]=count;}if(collision)fail++;else{surv.push_back(d);cout<<"survivor "<<d<<"\n";}}
cout<<"nonlisted exponent trials "<<count<<" exact necessary-condition rejections "<<fail<<" survivors "<<surv.size()<<" samples_per_exponent_cap "<<xs.size()<<"\n";
}
