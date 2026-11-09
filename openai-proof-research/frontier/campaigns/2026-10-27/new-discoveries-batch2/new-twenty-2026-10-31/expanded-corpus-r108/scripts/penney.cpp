#include <iostream>
#include <vector>
#include <cstdint>
using namespace std;
int C(int a,int b,int n){int s=0;for(int k=1;k<=n;k++)if((a&((1<<k)-1))==(b>>(n-k)))s+=1<<(k-1);return s;}
int main(int argc,char**argv){int n=atoi(argv[1]),M=1<<n;vector<int>self(M);for(int a=0;a<M;a++)self[a]=C(a,a,n); long long pairs=0,ties=0;for(int a=0;a<M/2;a++){int cand[4]={0,M-1,(a*2)&(M-1),((a*2)&(M-1))|1};int bn=1,bd=2; for(int b:cand)if(b!=a){int y=self[b]-C(b,a,n),x=self[a]-C(a,b,n);if(1LL*y*bd>1LL*bn*(x+y)){bn=y;bd=x+y;}}for(int b=0;b<M;b++)if(a!=b){pairs++;int y=self[b]-C(b,a,n),x=self[a]-C(a,b,n);if(1LL*y*bd>1LL*bn*(x+y)){cout<<"FAIL "<<n<<" A "<<a<<" B "<<b<<" prob "<<y<<"/"<<x+y<<" candidates "<<bn<<"/"<<bd<<endl;return 0;}if(1LL*y*bd==1LL*bn*(x+y)&&b!=cand[0]&&b!=cand[1]&&b!=cand[2]&&b!=cand[3]){ties++;if(ties<5)cout<<"OUTSIDE_TIE "<<n<<" "<<a<<" "<<b<<endl;}}}cout<<"PASS n="<<n<<" complement representatives="<<M/2<<" ordered pairs="<<pairs<<" outside ties="<<ties<<endl;}
