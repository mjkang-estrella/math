#include <cstdio>
#include <vector>
#include <cstdint>
#include <cstdlib>
int main(int argc,char**argv){int n=atoi(argv[1]),p=atoi(argv[2]); unsigned M=1u<<n;std::vector<uint8_t>a(M);std::vector<unsigned> N(n); for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(i!=j && ((i-j+n)%n<=p || (j-i+n)%n<=p))N[i]|=1u<<j;long long sums[12]={};unsigned long long fs[12]={};for(unsigned s=0;s<M;s++){if(s){unsigned b=s&-s;int i=__builtin_ctz(b);a[s]=std::max(a[s^b],(uint8_t)(1+a[(s^b)&~N[i]]));}for(int k=2;k<=8;k++)if(n>=(2*k-1)*p+1 && a[s]<k){sums[k]+=(__builtin_popcount(s)%2?-1:1);fs[k]++;}}for(int k=2;k<=8;k++)if(n>=(2*k-1)*p+1)printf("{\"n\":%d,\"p\":%d,\"k\":%d,\"dual_faces\":%llu,\"alternating_sum\":%lld,\"expected\":1}\n",n,p,k,fs[k],sums[k]);}
