#include <stdio.h>
#include <stdint.h>
#define max(a,b) ((a)>(b)?(a):(b))
#define min(a,b) ((a)<(b)?(a):(b))
#define bool int
#define false 0
#define true 1
int main(){
 for(int n=1;n<=7;n++){
 int eu[21],ev[21],en=0;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){eu[en]=i;ev[en++]=j;}
 long long tf=0,connected=0,noncb=0,minslack=1000000000,maxsigma=-1;long long B=0;
 for(int a=1;a<n;a++) B=max(B,1LL*a*(n-a)*(n-2*a)*(n-2*a));
 for(uint64_t mask=0;mask<(1ULL<<en);mask++){
 int adj[7]={},deg[7]={},m=0;bool tri=false;
 for(int k=0;k<(int)en;k++)if(mask>>k&1){int u=eu[k],v=ev[k]; if(adj[u]&adj[v]){tri=true;break;}adj[u]|=1<<v;adj[v]|=1<<u;deg[u]++;deg[v]++;m++;}
 if(tri)continue;tf++;int reach=1;for(int z=0;z<n;z++)for(int u=0;u<n;u++)if(reach>>u&1)reach|=adj[u];if(reach!=(1<<n)-1)continue;connected++;
 long long M=0;for(int u=0;u<n;u++)M+=deg[u]*deg[u];long long D=1LL*n*m-M,s=1LL*n*M-4LL*m*m;maxsigma=max(maxsigma,s);
 if(D){noncb++;minslack=min(minslack,D-(n-2));if(D<n-2){printf("GAP FAILURE %d %llu\n",n,(unsigned long long)mask);return 1;}}
 if(s>B){printf("CONJECTURE FAILURE %d %llu\n",n,(unsigned long long)mask);return 2;}
 }
 printf("n=%d trianglefree_labeled=%lld connected=%lld noncb=%lld min_gap_slack=%lld max_sigma=%lld B=%lld\n",n,tf,connected,noncb,noncb?minslack:0,maxsigma,B);
 }
 for(long long n=7;n<=10000;n++){
  long long a=1;while(8*a*(n-a)<n*n)a++;
  long long d1=8*a*(n-a)-n*n,d2=n*n-8*(a-1)*(n-a+1);
  long long d=min(d1,d2);
  if(d*d>16*(n-3)*(n-3)){printf("ROUND FAILURE %lld",n);return 3;}
 }
 printf("Integer bracketing verified n=7..10000 (diagnostic only).\n");
}
