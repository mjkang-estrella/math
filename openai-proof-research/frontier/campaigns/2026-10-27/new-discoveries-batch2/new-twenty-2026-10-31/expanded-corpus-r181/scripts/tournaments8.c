extern int printf(const char *,...);
extern void *calloc(unsigned long,unsigned long);
extern void free(void*);
extern int fflush(void*);
#define stdout ((void*)0)
int idx[10][10],subidx[10][10];unsigned char *orb[9];int p[10],k;
void perms(int j){if(j==k){unsigned m=0;int odd=k%2?k:k+1;for(int a=0;a<k;a++)for(int b=a+1;b<k;b++)if((p[b]-p[a]+odd)%odd<=odd/2)m|=1u<<subidx[a][b];orb[k][m]=1;return;}for(int a=j;a<k;a++){int t=p[j];p[j]=p[a];p[a]=t;perms(j+1);t=p[j];p[j]=p[a];p[a]=t;}}
int main(){for(int n=8;n<=8;n++){
 int b=0;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)idx[i][j]=b++;
 for(k=5;k<=n;k++){int z=0;for(int i=0;i<k;i++)for(int j=i+1;j<k;j++)subidx[i][j]=z++;orb[k]=calloc(1u<<z,1);for(int i=0;i<k;i++)p[i]=i;perms(0);}
 int mp[9][128][21],sz[9]={0};
 for(k=5;k<=n;k++)for(int s=0;s<(1<<n);s++)if(__builtin_popcount(s)==k){int v[10],z=0,t=0;for(int i=0;i<n;i++)if(s>>i&1)v[z++]=i;for(int i=0;i<k;i++)for(int j=i+1;j<k;j++)mp[k][sz[k]][t++]=idx[v[i]][v[j]];sz[k]++;}
 int mx[9],cnt[9]={0},bad[9]={0};unsigned witness[9]={0};for(k=5;k<=n;k++)mx[k]=-1;
 for(unsigned representative=0;representative<8*(1u<<21);representative++){ unsigned r=representative>>21; unsigned m=((representative&((1u<<21)-1))<<7)|((1u<<r)-1);for(k=5;k<=n;k++){
 int score=0;for(int s=0;s<sz[k];s++){unsigned sub=0;for(int i=0;i<k*(k-1)/2;i++)sub|=((m>>mp[k][s][i])&1u)<<i;score+=orb[k][sub];}
 if(score>mx[k]){mx[k]=score;cnt[k]=bad[k]=0;}if(score==mx[k]){cnt[k]++;if(!orb[n][m]){bad[k]++;witness[k]=m;}}
 }
 }
 for(k=5;k<=n;k++){printf("n=%d k=%d labelled_space=%u reduced_representatives=16777216 max=%d maximizers=%d noncanonical=%d witness=%u\n",n,k,1u<<b,mx[k],cnt[k],bad[k],witness[k]);free(orb[k]);}fflush(stdout);
}}
