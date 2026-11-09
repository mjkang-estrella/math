extern int printf(const char*,...);extern void *calloc(unsigned long,unsigned long);extern void free(void*);
typedef unsigned long long U;
static U dp[11][11][11], hist[70],total;static unsigned char *seen;static int N,L;
static int marked(U r){return (seen[r>>3]>>(r&7))&1;}
static void mark(U r){seen[r>>3]|=1<<(r&7);}
static U rankword(unsigned char*w){int a=0,b=0,c=0;U r=0;
 for(int i=0;i<L;i++){int x=w[i];if(x>0&&a<N)r+=dp[a+1][b][c];if(x>1&&b<a)r+=dp[a][b+1][c];if(x==0)a++;else if(x==1)b++;else c++;}return r;}
static void pro(unsigned char*w){unsigned char idx[30];int counts[3]={0};for(int i=0;i<L;i++)idx[i]=counts[w[i]]++;
 for(int i=0;i<L-1;i++){int x=w[i],y=w[i+1],j=idx[i],k=idx[i+1];if(x==y||(x==0&&j<=k)||(y==0&&k<=j))continue;w[i]=y;w[i+1]=x;idx[i]=k;idx[i+1]=j;}}
static void process(unsigned char*w,U rank){if(marked(rank))return;unsigned char v[30];for(int i=0;i<L;i++)v[i]=w[i];U r=rank;int len=0;
 do{mark(r);pro(v);r=rankword(v);len++;if(len>6*N){printf("bad orbit\n");return;}}while(r!=rank);
 hist[len]++;}
static void gen(int a,int b,int c,unsigned char*w,int i,U r){if(i==L){process(w,r);return;}if(a<N){w[i]=0;gen(a+1,b,c,w,i+1,r);r+=dp[a+1][b][c];}if(b<a){w[i]=1;gen(a,b+1,c,w,i+1,r);r+=dp[a][b+1][c];}if(c<a){w[i]=2;gen(a,b,c+1,w,i+1,r);}}
int run(int n){N=n;L=3*n;for(int a=n;a>=0;a--)for(int b=a;b>=0;b--)for(int c=a;c>=0;c--){if(a==n&&b==n&&c==n)dp[a][b][c]=1;else{dp[a][b][c]=0;if(a<n)dp[a][b][c]+=dp[a+1][b][c];if(b<a)dp[a][b][c]+=dp[a][b+1][c];if(c<a)dp[a][b][c]+=dp[a][b][c+1];}}
 total=dp[0][0][0];seen=calloc((total+7)/8,1);if(!seen)return 1;for(int i=0;i<70;i++)hist[i]=0;unsigned char w[30];gen(0,0,0,w,0,0);printf("n=%d total=%llu\n",n,total);U sum=0;for(int i=1;i<=6*n;i++)if(hist[i]){printf("orbit_size=%d count=%llu\n",i,hist[i]);sum+=i*hist[i];}free(seen);printf("accounted=%llu\n",sum);return sum!=total;}
