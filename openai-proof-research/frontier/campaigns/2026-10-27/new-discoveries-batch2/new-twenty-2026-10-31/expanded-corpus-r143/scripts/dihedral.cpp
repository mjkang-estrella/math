#include <bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){int lo=argc>1?atoi(argv[1]):3, hi=argc>2?atoi(argv[2]):13;
for(int n=lo;n<=hi;n++){int N=1<<n; unsigned all=N-1; auto rot=[&](unsigned x,int k){return ((x<<k)|(x>>(n-k)))&all;}; vector<unsigned> ss(N),dd(N),neg(N);for(int r=0;r<N;r++){for(int i=0;i<n;i++)if(r>>i&1){ss[r]|=rot(r,i);for(int j=0;j<n;j++)if(r>>j&1)dd[r]|=1u<<((i-j+n)%n);neg[r]|=1u<<((n-i)%n);}}vector<array<long long,3>>cnt(2*n+1);
for(int r=0;r<N;r++)for(int f=0;f<N;f++){unsigned rf=0,nrf=0;for(unsigned v=r;v;v&=v-1){int i=__builtin_ctz(v);rf|=rot(f,i);nrf|=rot(f,(n-i)%n);}int a=__builtin_popcount(ss[r]|dd[f])+__builtin_popcount(rf|nrf);int b=__builtin_popcount(dd[r]|dd[f])+__builtin_popcount(rf);cnt[__builtin_popcount((unsigned)r)+__builtin_popcount((unsigned)f)][(a>b)?0:(a<b)?1:2]++;}
cout<<"{\"n\":"<<n<<",\"counts_MSTD_MDTS_balanced\":[";for(int m=0;m<=2*n;m++){if(m)cout<<",";cout<<"["<<cnt[m][0]<<","<<cnt[m][1]<<","<<cnt[m][2]<<"]";}cout<<"]}"<<endl;
}}
