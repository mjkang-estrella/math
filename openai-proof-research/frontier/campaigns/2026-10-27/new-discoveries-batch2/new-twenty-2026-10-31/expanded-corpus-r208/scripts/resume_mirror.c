#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define N 20000000
#define B 100000
#define H (1<<22)
static uint64_t keys[H];static unsigned char present[H];
static unsigned slot(uint64_t w){unsigned s=(w*11400714819323198485ull)>>(64-22);while(present[s]&&keys[s]!=w)s=(s+1)&(H-1);return s;}
int main(){unsigned char *x=calloc(N,1);x[0]=x[1]=0;for(int i=2;i<N;i++){int k=i/3;x[i]=i%3==0?x[2*k]:i%3==1?x[2*k+1]:1-x[2*k+1];}
for(int len=1;len<=32;len++){for(int j=0;j<H;j++)present[j]=0;uint64_t mask=(1ull<<len)-1,w=0;for(int i=0;i<N;i++){w=((w<<1)|x[i])&mask;if(i>=len-1){unsigned s=slot(w);present[s]=1;keys[s]=w;}}
uint64_t *seen=malloc(B*sizeof(uint64_t));int ns=0,missing=0;w=0;for(int i=0;i<B;i++){w=((w<<1)|x[i])&mask;if(i>=len-1){if(!present[slot(mask^w)]){if(missing<5)printf("missing_length=%d start=%d word=%llu\n",len,i-len+1,(unsigned long long)w);missing++;}ns++;}}free(seen);printf("length=%d prefix_starts=%d complement_missing_occurrences=%d ambient_prefix=%d\n",len,ns,missing,N);fflush(stdout);}free(x);return 0;}
