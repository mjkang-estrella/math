#include <bits/stdc++.h>
using namespace std;using U=uint64_t;
int main(int argc,char**argv){int m=atoi(argv[1]),n=atoi(argv[2]),N=m*n;assert(N<=63);vector<U> lo(N),hi(N);vector<vector<int>> pred(N),succ(N);for(int i=0;i<m;i++)for(int j=0;j<n;j++){int x=i*n+j;for(int a=0;a<m;a++)for(int b=0;b<n;b++){if(a<=i&&b<=j)lo[x]|=1ULL<<(a*n+b);if(a>=i&&b>=j)hi[x]|=1ULL<<(a*n+b);}if(i)pred[x].push_back(x-n);if(j)pred[x].push_back(x-1);if(i+1<m)succ[x].push_back(x+n);if(j+1<n)succ[x].push_back(x+1);}
auto valid=[&](U s){for(int x=0;x<N;x++)if(!(s>>x&1)&&(s&lo[x])&&(s&hi[x]))return false;return true;};
auto row=[&](U s){for(int x=N-1;x>=0;x--){U b=1ULL<<x;bool ok=true;if(s&b)ok=!((s&(lo[x]^b))&&(s&(hi[x]^b)));else{for(int p:pred[x])if(!(s>>p&1)&&(s&lo[p]))ok=false;for(int q:succ[x])if(!(s>>q&1)&&(s&hi[q]))ok=false;}if(ok)s^=b;}return s;};
vector<U> opts{0};for(int a=0;a<n;a++)for(int b=a;b<n;b++)opts.push_back(((1ULL<<(b-a+1))-1)<<a);
unordered_set<U> states;function<void(int,U)> gen=[&](int i,U s){if(i==m){if(valid(s))states.insert(s);return;}for(U t:opts)gen(i+1,s|(t<<(i*n)));};gen(0,0);size_t total=states.size(),orbits=0,maxlen=0;U even=0;for(int i=0;i<m;i++)for(int j=0;j<n;j++)if((i+j)%2==0)even|=1ULL<<(i*n+j);
while(!states.empty()){U start=*states.begin(),s=start;long long sum=0;size_t len=0;do{assert(states.erase(s)==1);sum+=2*__builtin_popcountll(s&even)-__builtin_popcountll(s);len++;s=row(s);}while(s!=start);orbits++;maxlen=max(maxlen,len);if(sum){cout<<"FAIL m "<<m<<" n "<<n<<" start "<<start<<" len "<<len<<" sum "<<sum<<endl;return 1;}}
cout<<"m "<<m<<" n "<<n<<" states "<<total<<" orbits "<<orbits<<" max_length "<<maxlen<<" all_orbit_sums_zero true"<<endl;
}
