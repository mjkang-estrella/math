#include <vector>
#include <numeric>
#include <iostream>
using namespace std;
vector<long long> mul(const vector<long long>&a,const vector<long long>&b,int n){int r=a.size();vector<long long>c(r);for(int i=0;i<r;i++)for(int j=0;j<r;j++)c[(i+j)%r]=(c[(i+j)%r]+a[i]*b[j])%n;return c;}
bool prime(int n){if(n<2)return false;for(int d=2;d*d<=n;d++)if(n%d==0)return false;return true;}
int main(){long count=0,eligible=0,passed=0;for(int n=2;n<=2000;n++)for(int r=2;r<=40;r++){if(gcd(n,r)!=1)continue;count++;if(prime(n)||((long long)n*n)%r==1)continue;eligible++;vector<long long>a(r),b(r),want(r);a[0]=n-1;a[1]=1;b[0]=1;want[n%r]=1;want[0]=(want[0]+n-1)%n;int e=n;while(e){if(e&1)b=mul(a,b,n);a=mul(a,a,n);e>>=1;}if(b==want){passed++;cout<<"WITNESS "<<n<<" "<<r<<"\n";}}cout<<"space n=2..2000 r=2..40 coprime pairs="<<count<<" composite and n^2!=1 mod r candidates="<<eligible<<" violations="<<passed<<"\n";}
