#include <cstdio>
#include <vector>
int main(){for(int n=2;n<=26;n+=2){long long total=0,bal=0; unsigned lim=1u<<(n-1);for(unsigned mask=0;mask<lim;mask++){int p[30],start=0;for(int j=1;j<=n;j++)if(j==n||(mask>>(j-1)&1)){for(int i=start;i<j;i++)p[i]=n-j+i-start;start=j;}int x=0,c=0;do{x=p[x];c++;}while(x!=0&&c<=n);if(c==n){total++;bal+=bool(mask>>(n/2-1)&1);}}printf("{\"n\":%d,\"compositions\":%u,\"cyclic\":%lld,\"balanced_cyclic\":%lld}\n",n,lim,total,bal);fflush(stdout);}}
