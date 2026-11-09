#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
int n,k,N,best; uint64_t bestq; long long sets=0,answers=0;
int residual(uint64_t q,uint64_t a){
 uint64_t reach=1;int total=0,off=0;
 for(int row=1;row<=n;row++){
  uint64_t mask=(1ull<<row)-1, known=(q>>off)&mask, right=(a>>off)&mask;
  total+=__builtin_popcountll(reach&~known);
  uint64_t leftReach=reach&(~known|~right),rightReach=reach&(~known|right);
  reach=(leftReach|(rightReach<<1));off+=row;
 }
 return total;
}
void evaluate(uint64_t q){
 sets++; int worst=0;uint64_t a=q;
 while(true){answers++;worst=max(worst,residual(q,a));if(worst>=best)return;
 if(!a)break;a=(a-1)&q;}
 best=worst;bestq=q;
}
void choose(int i,int left,uint64_t q){if(!left){evaluate(q);return;}for(int j=i;j<=N-left;j++)choose(j+1,left-1,q|(1ull<<j));}
int main(int argc,char**argv){n=stoi(argv[1]);k=stoi(argv[2]);N=n*(n+1)/2;if(N>=63)return 2;best=N+1;choose(0,k,0);cout<<"{\"n\":"<<n<<",\"k\":"<<k<<",\"query_sets\":"<<sets<<",\"answers_evaluated\":"<<answers<<",\"minimax_remaining_unknown_reachable\":"<<best<<",\"best_first_batch_mask\":"<<bestq<<"}\n";}
