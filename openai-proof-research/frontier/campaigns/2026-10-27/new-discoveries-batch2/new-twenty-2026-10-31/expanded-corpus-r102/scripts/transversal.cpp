#include <bits/stdc++.h>
using namespace std;
int main(){mt19937 gen(102);for(int p:{3,5,7,11,13,17}){int n=p*p,m=n*n,best=INT_MAX;long long moves=0;vector<int> bestv;
for(int run=0;run<12;run++){vector<int> t(n),cnt(m);auto diff=[&](int a,int b){return ((a/n-b/n+n)%n)*n+(a%n-b%n+n)%n;};
for(int x=0;x<p;x++)for(int y=0;y<p;y++){int i=x*p+y;t[i]=(x+p*(run%3==0?0:gen()%p))*n+y+p*(run%3==0?0:gen()%p);}
int val=0;for(int a:t)for(int b:t)if(cnt[diff(a,b)]++==0)val++;auto alter=[&](int i,int nt){for(int j=0;j<n;j++)if(j!=i){if(--cnt[diff(t[i],t[j])]==0)val--;if(--cnt[diff(t[j],t[i])]==0)val--;}t[i]=nt;for(int j=0;j<n;j++)if(j!=i){if(cnt[diff(t[i],t[j])]++==0)val++;if(cnt[diff(t[j],t[i])]++==0)val++;}};
for(int k=0;k<50000;k++){int i=1+gen()%(n-1),old=t[i],ov=val;int nt=(i/p+p*(gen()%p))*n+i%p+p*(gen()%p);alter(i,nt);double temp=0.15+3.0*(1.0-double(k%10000)/10000);if(val>ov&&generate_canonical<double,32>(gen)>exp((ov-val)/temp))alter(i,old);moves++;if(val<best){best=val;bestv=t;}}
}cout<<"p "<<p<<" moves "<<moves<<" best "<<best<<" box "<<(2*p-1)*(2*p-1)<<" witness ";for(int x:bestv)cout<<x<<",";cout<<endl;}}
