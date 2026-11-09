#include <stdio.h>
#include <stdlib.h>
#include <math.h>
static unsigned seed=237;
static unsigned rng(){seed=1664525*seed+1013904223;return seed;}
int main(){
for(int n=6;n<=12;n+=2){int N=1<<(n/2),U=1<<(n-1);int univ[4096],z=0;
for(int x=0;x<(1<<n);x++)if(!(__builtin_popcount((unsigned)x)&1))univ[z++]=x;
for(int regime=0;regime<3;regime++){int s=regime==0?3:regime==1?N/2:N-(1<<(n/4));if(s<3)continue;int k=N+s,target=s*N/2,best=100000000;
long proposals=0;int completed=0;
for(int restart=0;restart<30;restart++){
int A[256],used[8192]={0},count=0;
// Begin with the classical paired-coordinate eventown plus random extra even vectors.
for(int b=0;b<N;b++){int x=0;for(int j=0;j<n/2;j++)if(b>>j&1)x|=3<<(2*j);A[count++]=x;used[x]=1;}
while(count<k){int x=univ[rng()%U];if(!used[x]){used[x]=1;A[count++]=x;}}
int obj=0;for(int i=0;i<k;i++)for(int j=0;j<i;j++)obj+=__builtin_parity((unsigned)(A[i]&A[j]));
for(int t=0;t<30000;t++){
 int i=rng()%k,y=univ[rng()%U];if(used[y])continue;proposals++;int delta=0;
 for(int j=0;j<k;j++)if(j!=i)delta+=__builtin_parity((unsigned)(y&A[j]))-__builtin_parity((unsigned)(A[i]&A[j]));
 double temp=(1.0-(double)t/30000)*2.0+0.05;
 if(delta<=0||(double)(rng()>>8)/16777216.0<exp(-delta/temp)){used[A[i]]=0;used[y]=1;A[i]=y;obj+=delta;}
 if(obj<best){best=obj;if(best<target){printf("COUNTEREXAMPLE n=%d s=%d objective=%d target=%d sets=",n,s,best,target);for(int j=0;j<k;j++)printf("%d,",A[j]);puts("");return 0;}}
}completed++;
}
printf("n=%d s=%d k=%d best=%d bound=%d restarts=%d proposals=%ld\n",n,s,k,best,target,completed,proposals);fflush(stdout);
}}
}
