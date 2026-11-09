extern int printf(const char*,...); extern void *calloc(unsigned long,unsigned long); extern int atoi(const char*);
int main(int argc,char**argv){int N=atoi(argv[1]);__int128 *R=calloc((unsigned long)7*(N+2),sizeof(__int128));
#define V(j,n) R[(unsigned long)(j)*(N+2)+(n)]
V(6,0)=1;int C[7][7]={{0}};for(int j=0;j<=6;j++){C[j][0]=C[j][j]=1;for(int i=1;i<j;i++)C[j][i]=C[j-1][i-1]+C[j-1][i];}
for(int n=1;n<=N+1;n++)for(int j=0;j<=6;j++)for(int i=0;i<=j;i++)for(int h=0;h<=6-j;h++)if(n>=i+h&&(n-i-h)%2==0)V(j,n)+=C[j][i]*C[6-j][h]*V(j-i+h,(n-i-h)/2);
for(int j=0;j<=6;j+=6){int bad=0,last=-1;for(int n=0;n<=N;n++)if(V(j,n)>=V(j,n+1)){bad++;last=n;if(n>=(j?37:5)){printf("FAIL j=%d n=%d\n",j,n);}}printf("j=%d N=%d total nonincrease=%d last=%d\n",j,N,bad,last);}return 0;}
