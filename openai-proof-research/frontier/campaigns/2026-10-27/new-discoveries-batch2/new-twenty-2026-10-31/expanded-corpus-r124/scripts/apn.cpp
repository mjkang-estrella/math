#include <bits/stdc++.h>
using namespace std;
int main(){for(int n:{5,7,9,11}){int q=1<<n,pol=n==5?0x25:n==7?0x83:n==9?0x211:0x805;auto mul=[&](int a,int b){int r=0;for(;b;b>>=1){if(b&1)r^=a;a<<=1;if(a&q)a^=pol;}return r;};auto pw=[&](int a,int e){int r=1;for(;e;e>>=1,a=mul(a,a))if(e&1)r=mul(r,a);return r;};vector<int>M(q*q);for(int a=0;a<q;a++)for(int b=0;b<q;b++)M[a*q+b]=mul(a,b);int s=(1<<((n-1)/2))+(1<<(n%4==1?(n-1)/4:(3*n-1)/4))-1;vector<int>B;vector<bool>in(q);for(int x=0;x<q;x++)in[pw(x+0,s)^pw(x^1,s)]=1;for(int x=0;x<q;x++)if(in[x])B.push_back(x);vector<long long>cnt(q);int stab=0;
for(int a=1;a<q;a++){int inv=pw(a,q-2);for(int b=0;b<q;b++){if(in[b]&&in[b^a])for(int y:B)cnt[M[inv*q+(y^b)]]++;bool ok=true;for(int y:B)if(!in[M[a*q+y]^b]){ok=false;break;}stab+=ok;}}
long long lo=LLONG_MAX,hi=0;for(int t=2;t<q;t++){lo=min(lo,cnt[t]);hi=max(hi,cnt[t]);}cout<<"n="<<n<<" modulus="<<pol<<" s="<<s<<" block="<<B.size()<<" stabilizer="<<stab<<" triple_counts_min="<<lo<<" max="<<hi<<" expected="<<1LL*q*(q-4)/8<<endl;
}}
