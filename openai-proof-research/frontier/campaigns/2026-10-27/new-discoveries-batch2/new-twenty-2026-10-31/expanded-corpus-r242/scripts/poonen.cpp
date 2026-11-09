#include <cstdint>
#include <cstdio>
#include <vector>
#include <chrono>
using U=uint64_t;
int n,N;U all;long long count,eligible,hyp,fail;
U close(U f){bool change=true;while(change){change=false;U x=f;while(x){int a=__builtin_ctzll(x);x&=x-1;U y=f;while(y){int b=__builtin_ctzll(y);y&=y-1;U bit=U(1)<<(a&b);if(!(f&bit)){f|=bit;change=true;}}}}return f;}
void check(U f){count++;int size=__builtin_popcountll(f);if(size<=1)return;int un=0;U sig[5]={};for(int a=0;a<N;a++)if(f>>a&1){un|=a;for(int j=0;j<n;j++)if(a>>j&1)sig[j]|=U(1)<<a;}
 if(un!=N-1)return;for(int i=0;i<n;i++)for(int j=0;j<i;j++)if(sig[i]==sig[j])return;eligible++;int low=0,alpha=-1;for(int i=0;i<n;i++)if(2*__builtin_popcountll(sig[i])<=size){low++;alpha=i;}if(low!=1)return;hyp++;U expected=U(1)<<(N-1);for(int a=0;a<N;a++)if(!(a>>alpha&1))expected|=U(1)<<a;if(f!=expected){fail++;printf("failure n=%d family=%llu alpha=%d\n",n,(unsigned long long)f,alpha);}}
int main(){for(n=1;n<=5;n++){N=1<<n;all=(U(1)<<N)-1;count=eligible=hyp=fail=0;U f=close(0);while(true){check(f);bool found=false;for(int i=N-1;i>=0;i--)if(!(f>>i&1)){U lower=(U(1)<<i)-1;U g=close((f&lower)|(U(1)<<i));if((g&lower)==(f&lower)){f=g;found=true;break;}}if(!found)break;}printf("n=%d closed_families=%lld full_ground_separating=%lld unique_low=%lld failures=%lld\n",n,count,eligible,hyp,fail);fflush(stdout);}}
