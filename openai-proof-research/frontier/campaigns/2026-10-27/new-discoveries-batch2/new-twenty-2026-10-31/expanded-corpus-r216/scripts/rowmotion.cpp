#include <bits/stdc++.h>
using namespace std;using U=uint64_t;
int main(int argc,char**argv){int m=atoi(argv[1]),n=atoi(argv[2]),N=m*n; if(N>63)return 2; U full=(1ULL<<N)-1;vector<U>lo(N),hi(N);for(int x=0;x<N;x++)for(int y=0;y<N;y++)if(x!=y){if(y/n<=x/n&&y%n<=x%n)lo[x]|=1ULL<<y;if(y/n>=x/n&&y%n>=x%n)hi[x]|=1ULL<<y;}
vector<U>ideals;function<void(int,int,U)>gen=[&](int i,int prev,U s){if(i==m){ideals.push_back(s);return;}for(int k=0;k<=prev;k++)gen(i+1,k,s|(((1ULL<<k)-1)<<(i*n)));};gen(0,n,0);
unordered_set<U>all;for(U a:ideals)for(U b:ideals)if(!(b&~a))all.insert(a&~b);cerr<<"ideals "<<ideals.size()<<" convex_sets "<<all.size()<<endl;
auto row=[&](U s){for(int x=N-1;x>=0;x--){U bit=1ULL<<x;if(s&bit){if(!(s&lo[x])||!(s&hi[x]))s^=bit;}else{bool ok=true;U t=s&lo[x];while(t&&ok){int y=__builtin_ctzll(t);t&=t-1;if((hi[y]&lo[x])&~s)ok=false;}t=s&hi[x];while(t&&ok){int y=__builtin_ctzll(t);t&=t-1;if((lo[y]&hi[x])&~s)ok=false;}if(ok)s|=bit;}}return s;};
auto stat=[&](U s){int z=0;for(int x=0;x<N;x++)if(s>>x&1){z+=!(s&hi[x]);z-=!(s&lo[x]);}return z;};
size_t orbits=0,maxlen=0,checked=0;while(!all.empty()){U a=*all.begin(),s=a;long sum=0;size_t len=0;do{if(!all.erase(s)){cerr<<"NOT PERMUTATION";return 3;}sum+=stat(s);len++;s=row(s);}while(s!=a);orbits++;checked+=len;maxlen=max(maxlen,len);if(sum){cout<<"COUNTEREXAMPLE "<<m<<" "<<n<<" seed "<<a<<" len "<<len<<" sum "<<sum<<endl;return 1;}}
cout<<m<<" "<<n<<" checked "<<checked<<" orbits "<<orbits<<" longest "<<maxlen<<" all sums zero\n";}
