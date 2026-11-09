#include <iostream>
#include <cstdint>
#include <cstdlib>
using U=uint64_t;
U mx(U u,U v,int n){U d[16][16]{}; // suffix state, encode a=0,b=1
 for(int i=n;i>=0;--i)for(int j=n;j>=0;--j){
  if(i==n){d[i][j]=v&((U(1)<<(n-j))-1);continue;}
  if(j==n){d[i][j]=u&((U(1)<<(n-i))-1);continue;}
  int a=(u>>(n-i-1))&1,b=(v>>(n-j-1))&1,len=2*n-i-j;
  U x=d[i+1][j]|(U(a)<<(len-1)), y=d[i][j+1]|(U(b)<<(len-1));
  d[i][j]=a==b?(x>y?x:y):(a==0?x:y);
 }return d[0][0];}
int main(int argc,char**argv){int n=atoi(argv[1]);U count=U(1)<<n, pairs=0,prior=0;bool any=false;
 for(U w=0;w<count;++w){U square=mx(w,w,n);if(any&&prior>=square){std::cout<<"FAIL prior at "<<n<<" "<<w<<"\n";return 1;}
  for(U x=0;x<w;++x){U z=mx(x,w,n);++pairs;if(z>=square){std::cout<<"FAIL n="<<n<<" x="<<x<<" w="<<w<<" max="<<z<<" square="<<square<<"\n";return 1;}if(!any||z>prior)prior=z;any=true;}
  // old diagonal pairs are among the mixed pairs for the next w.
  if(!any||square>prior)prior=square;any=true;
 }
 std::cout<<"n="<<n<<" words="<<count<<" unordered_distinct_pairs="<<pairs<<" strict_leading_square_criterion=PASS\n";
}
