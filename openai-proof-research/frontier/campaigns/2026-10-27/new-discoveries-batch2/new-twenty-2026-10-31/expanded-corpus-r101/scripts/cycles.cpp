#include <vector>
#include <iostream>
#include <cstdint>
int main(){for(int n=1;n<=11;n++){int m=2*n,b=m-1,N=1<<b;std::vector<uint64_t> dp((size_t)N*b,0);for(int j=0;j<b;j++)dp[(size_t)(1<<j)*b+j]=1;for(int s=1;s<N;s++)for(int j=0;j<b;j++)if(s>>j&1){uint64_t v=dp[(size_t)s*b+j];if(!v)continue;for(int k=0;k<b;k++)if(!(s>>k&1)&&((j+2<k+2)||((j+2)%2==0&&(k+2)%2==1)))dp[(size_t)(s|(1<<k))*b+k]+=v;}uint64_t ans=0;for(int j=0;j<b;j++)if((j+2)%2==0)ans+=dp[(size_t)(N-1)*b+j];std::cout<<n<<" "<<ans<<std::endl;}}
