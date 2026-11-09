#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>
using namespace std;
int main(int argc,char**argv){int n=argc>1?stoi(argv[1]):35;set<array<int,4>> reps;long long all=0,tests=0;auto start=chrono::steady_clock::now();
for(int b=1;b<n;b++)for(int c=b+1;c<n;c++)for(int d=c+1;d<n;d++){array<int,4>a{0,b,c,d},best=a;for(int shift:a)for(int u=1;u<n;u++)if(gcd(u,n)==1){array<int,4>x;for(int j=0;j<4;j++)x[j]=((a[j]-shift+n)*u)%n;sort(x.begin(),x.end());best=min(best,x);}reps.insert(best);all++;}
int done=0;for(auto a:reps){for(int b=0;b<n;b++)for(int c=b;c<n;c++)for(int d=c;d<n;d++){array<int,4>bs{0,b,c,d};bool ok=false;do{array<int,4>s;for(int j=0;j<4;j++)s[j]=(a[j]+bs[j])%n;sort(s.begin(),s.end());if(adjacent_find(s.begin(),s.end())==s.end()){ok=true;break;}}while(next_permutation(bs.begin(),bs.end()));tests++;if(!ok){cout<<"COUNTEREXAMPLE "<<n<<" A ";for(int x:a)cout<<x<<",";cout<<" B 0,"<<b<<","<<c<<","<<d<<endl;return 1;}}done++;}
cout<<"{\"n\":"<<n<<",\"k\":4,\"A_zero_subsets\":"<<all<<",\"affine_A_orbits\":"<<reps.size()<<",\"completed_A_orbits\":"<<done<<",\"B_multisets_containing_zero_per_A\":"<<((long long)n*(n+1)*(n+2)/6)<<",\"tests\":"<<tests<<",\"counterexamples\":0,\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"}"<<endl;}
