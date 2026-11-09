#include <vector>
#include <iostream>
#include <algorithm>
int main(){for(int p=1;p<=5;p++)for(int q=1;q<=5;q++){int Q=p+q;if(Q>8)continue;for(int n=3;n<=5;n++){int z=1;for(int j=0;j<n;j++)z*=Q;if(z>4096)continue;int N=std::min(4000000,std::max(100000,4*z*z));std::vector<unsigned char>t(N);for(int i=1;i<N;i++)t[i]=t[i/Q]^(i%Q>=p);int bound=z+Q-2;if(p==q && n%2==0)bound=z+Q+(p==1?2:0);else if(p==q && p==1)bound=z+Q;else if(std::min(p,q)==1)bound=z+Q-1;int max=0,bd=0,bs=0;long long covered=0;for(int d=1;d<=z+1;d++){// all starts, bounded total ~150 million per case
if(1LL*N*(z+1)>150000000 && d!=z-1 && d!=z+1 && d>150000000/N)continue;
covered++;for(int r=0;r<d;r++){int run=0;for(int i=r;i<N;i+=d){run=(i>=d && t[i]==t[i-d])?run+1:1;if(run>max){max=run;bd=d;bs=i-(run-1)*d;}}}}
std::cout<<p<<' '<<q<<' '<<n<<" prefix "<<N<<" differences "<<covered<<" bound "<<bound<<" observed "<<max<<" d "<<bd<<" start "<<bs<<" violation "<<(max>bound)<<std::endl;
}}}
