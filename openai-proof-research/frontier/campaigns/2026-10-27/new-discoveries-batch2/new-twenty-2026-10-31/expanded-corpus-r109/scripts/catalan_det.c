// det(CG_n) mod two primes for n in [lo,hi] (step), using Gaussian elimination with row pivoting.
// Adjacency: for i>j>=1, A[i][j] = ([z^{i-1-j}] C(z)^j) mod 2, C = Catalan GF; symmetric, zero diagonal.
// Header-free: the host has no libc headers for the bundled clang; explicit prototypes.
int printf(const char*,...); int atoi(const char*); void*calloc(unsigned long,unsigned long); void*malloc(unsigned long); int fflush(void*);
typedef unsigned long size_t; typedef unsigned long long u64; typedef __uint128_t u128;
static int N;
static unsigned char *adj; // adj[i*N+j], 1-based i,j < N+1
// ballot numbers mod 2: B(m,j) = [z^m] C^j = j/(2m+j) binom(2m+j,m). Compute via recurrence mod 2:
// C^j coefficients: c_j(m) = c_{j-1}(m) + c_{j+1}(m-1) (since C = 1 + z C^2 -> C^j = C^{j-1} + z C^{j+1}).
// Build table T[m][j] mod 2 for m+j <= N.
static u64 pw(u64 a,u64 e,u64 p){u64 r=1;a%=p;while(e){if(e&1)r=(u128)r*a%p;a=(u128)a*a%p;e>>=1;}return r;}
static u64 detmod(int n,u64 p,u64*M){
  for(int i=0;i<n;i++)for(int j=0;j<n;j++)M[i*n+j]=adj[(i+1)*(N+2)+(j+1)];
  u64 d=1;
  for(int c=0;c<n;c++){
    int r=-1;for(int i=c;i<n;i++)if(M[i*n+c]){r=i;break;}
    if(r<0)return 0;
    if(r!=c){for(int j=0;j<n;j++){u64 t=M[r*n+j];M[r*n+j]=M[c*n+j];M[c*n+j]=t;} d=(p-d)%p;}
    d=(u128)d*M[c*n+c]%p; u64 inv=pw(M[c*n+c],p-2,p);
    for(int i=c+1;i<n;i++){u64 f=M[i*n+c];if(!f)continue;f=(u128)f*inv%p;
      u64 g=p-f; for(int j=c;j<n;j++){M[i*n+j]=(M[i*n+j]+g*M[c*n+j])%p;}}
  }
  return d;
}
int main(int argc,char**argv){
  int lo=atoi(argv[1]),hi=atoi(argv[2]),step=atoi(argv[3]); N=hi;
  // T[m][j], m from 0..N, j from 0..N+1
  int W=N+3; unsigned char*T=calloc((size_t)W*W,1);
  for(int m=0;m<W;m++)T[m*W+0]=(m==0);
  // c_j(m) = c_{j-1}(m) + c_{j+1}(m-1): fill by increasing m, and for fixed m, j increasing needs c_{j+1}(m-1) known.
  for(int m=0;m<W-1;m++)for(int j=1;j<W-1;j++)T[m*W+j]=(T[m*W+j-1]+(m>0?T[(m-1)*W+j+1]:0))&1;
  adj=calloc((size_t)(N+2)*(N+2),1);
  for(int i=1;i<=N;i++)for(int j=1;j<i;j++){int m=i-1-j;unsigned char v=T[m*W+j];adj[i*(N+2)+j]=v;adj[j*(N+2)+i]=v;}
  u64*M=malloc(sizeof(u64)*(size_t)N*N);
  u64 p1=2147483647ULL,p2=2147483629ULL; // primes < 2^31 so products fit in 64 bits
  for(int n=lo;n<=hi;n+=step){u64 a=detmod(n,p1,M);u64 b=a?1:detmod(n,p2,M);printf("%d %llu %d\n",n,a,(a==0&&b==0)?1:0);fflush(0);}
}
