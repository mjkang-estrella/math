extern int printf(const char*,...);extern int fflush(void*);
unsigned rng=181;unsigned randu(){rng^=rng<<13;rng^=rng>>17;rng^=rng<<5;return rng;}
unsigned adj[16],sub[20000];int ns,n,k;unsigned long evaluations;
int score(){int answer=0; evaluations++;for(int ss=0;ss<ns;ss++){unsigned s=sub[ss];int ok=1;for(int v=0;v<n&&ok;v++)if(s>>v&1){unsigned nb=adj[v]&s;if(__builtin_popcount(nb)!=(k-1)/2){ok=0;break;}unsigned degrees=0;for(int u=0;u<n;u++)if(nb>>u&1){int d=__builtin_popcount(adj[u]&nb);if(degrees>>d&1){ok=0;break;}degrees|=1u<<d;}}answer+=ok;}return answer;}
void carousel(){int odd=n%2?n:n+1;for(int i=0;i<n;i++){adj[i]=0;for(int j=0;j<n;j++)if(i!=j&&(j-i+odd)%odd<=odd/2)adj[i]|=1u<<j;}}
void flip(int i,int j){adj[i]^=1u<<j;adj[j]^=1u<<i;}
int main(){for(n=9;n<=14;n++)for(k=5;k<=9&&k<=n;k+=2){ns=0;for(unsigned s=0;s<(1u<<n);s++)if(__builtin_popcount(s)==k)sub[ns++]=s;carousel();int base=score(),maximum=base;unsigned long start=evaluations;int steps=0;
 for(int restart=0;restart<24;restart++){carousel();if(restart%2){for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)if(randu()%2)flip(i,j);}else for(int t=0;t<1+restart/2;t++){int i=randu()%n,j=randu()%n;if(i!=j)flip(i,j);}
 int current=score();for(int step=0;step<30;step++){int best=current,bi=-1,bj=-1;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){flip(i,j);int v=score();flip(i,j);if(v>best){best=v;bi=i;bj=j;}}if(bi<0)break;flip(bi,bj);current=best;steps++;}if(current>maximum)maximum=current;if(current>base){printf("FAIL n=%d k=%d base=%d value=%d rows=",n,k,base,current);for(int i=0;i<n;i++)printf("%u,",adj[i]);printf("\n");}}
 printf("n=%d k=%d restarts=24 baseline=%d best=%d score_evaluations=%lu improving_steps=%d\n",n,k,base,maximum,evaluations-start,steps);fflush(0);}}
