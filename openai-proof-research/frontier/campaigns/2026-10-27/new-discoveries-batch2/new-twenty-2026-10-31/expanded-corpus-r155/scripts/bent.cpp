#include <bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){int n=atoi(argv[1]),d=atoi(argv[2]);unsigned N=1u<<n;set<unsigned> seen; vector<vector<uint64_t>> orb;
for(unsigned s=1;s<N;s++) if(__builtin_popcount(s)==d && !seen.count(s)){
 vector<unsigned>o; unsigned t=s;do{o.push_back(t);seen.insert(t);t=((t<<1)&(N-1))|(t>>(n-1));}while(t!=s);
 vector<uint64_t>v(N/64);for(unsigned x=0;x<N;x++){int b=0;for(auto m:o)b^=((x&m)==m);if(b)v[x/64]|=1ull<<(x%64);}orb.push_back(v);
}
uint64_t cases=1ull<<orb.size(),lim=argc>3?strtoull(argv[3],0,10):cases;lim=min(lim,cases);vector<uint64_t>tt(N/64);vector<int>w(N);uint64_t passes=0;int target=1<<(n/2);uint64_t prev=0;
cout<<"n "<<n<<" degree "<<d<<" orbits "<<orb.size()<<" total "<<cases<<" testing "<<lim<<endl;
for(uint64_t m=0;m<lim;m++){uint64_t g=m^(m>>1);if(m){int j=__builtin_ctzll(g^prev);for(unsigned k=0;k<tt.size();k++)tt[k]^=orb[j][k];}prev=g;
 int weight=0;for(auto x:tt)weight+=__builtin_popcountll(x);if(abs((int)N-2*weight)!=target)continue;passes++;
 for(unsigned x=0;x<N;x++)w[x]=((tt[x/64]>>(x%64))&1)?-1:1;
 for(unsigned len=1;len<N;len*=2)for(unsigned st=0;st<N;st+=2*len)for(unsigned j=0;j<len;j++){int a=w[st+j],b=w[st+j+len];w[st+j]=a+b;w[st+j+len]=a-b;}
 bool ok=true;for(auto x:w)if(abs(x)!=target){ok=false;break;}if(ok){cout<<"BENT orbit mask "<<g<<endl;return 0;}
}cout<<"tested "<<lim<<" weight-passed "<<passes<<" bent 0"<<endl;
}
