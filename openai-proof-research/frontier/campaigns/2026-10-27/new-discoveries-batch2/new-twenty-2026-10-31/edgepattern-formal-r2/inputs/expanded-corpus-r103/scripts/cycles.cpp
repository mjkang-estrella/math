#include <vector>
#include <iostream>
#include <cstdint>
#include <cstdlib>
using namespace std;
vector<uint64_t> counts(int n,bool d){
 vector<uint64_t> out(1<<n,0);
 for(int s=0;s<n;s++){
  int m=n-s;vector<uint64_t>dp((1<<m)*m,0);dp[m]=1;
  auto edge=[&](int a,int b){a+=s+1;b+=s+1;return d? (a%2? a<=b:a>=b): (a<=b || (a%2==0 && b%2==1));};
  vector<int> to(m);for(int a=0;a<m;a++)for(int b=1;b<m;b++)if(edge(a,b))to[a]|=1<<b;
  for(int mask=1;mask<(1<<m);mask+=2){
   for(int a=0;a<m;a++)if(auto c=dp[mask*m+a]){
    if(edge(a,0))out[mask<<s]+=c;
    int todo=to[a]&~mask;
    while(todo){int b=__builtin_ctz(todo);todo&=todo-1;dp[(mask|(1<<b))*m+b]+=c;}
   }
  }
 }
 return out;
}
int main(int argc,char**argv){int n=argc>1?atoi(argv[1]):18;auto a=counts(n,0),b=counts(n,1);int bad=0;for(int i=1;i<(1<<n);i++)if(a[i]!=b[i]){bad++;cout<<"MISMATCH "<<i<<" "<<a[i]<<" "<<b[i]<<"\n";}cout<<"n "<<n<<" subsets "<<(1<<n)-1<<" mismatches "<<bad<<" full_cycle_count "<<a.back()<<"\n";}
