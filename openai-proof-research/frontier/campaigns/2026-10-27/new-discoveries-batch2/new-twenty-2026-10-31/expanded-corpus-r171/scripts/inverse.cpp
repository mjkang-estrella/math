#include <cstdint>
#include <vector>
#include <cstdio>
#include <cstdlib>
// Full bitboard recursion. A legal move inserts a 1 without creating k consecutive 1s.
int main(int argc,char**argv){int k=atoi(argv[1]),N=atoi(argv[2]);
for(int n=0;n<=N;n++){
 uint32_t end=1u<<n;std::vector<unsigned char> sg(end,255);uint64_t states=0;
 for(uint32_t m=end;m-->0;){
  uint32_t run=m;for(int j=1;j<k;j++)run&=m>>j;if(run)continue;
  uint32_t seen=0;for(int i=0;i<n;i++)if(!(m>>i&1)){
    unsigned char v=sg[m|(1u<<i)];if(v!=255)seen|=1u<<v;
  }
  unsigned char v=0;while(seen>>v&1)v++;sg[m]=v;states++;
 }
 printf("k=%d n=%d sg=%d legal_states=%llu\n",k,n,sg[0],(unsigned long long)states);fflush(stdout);
}
}
