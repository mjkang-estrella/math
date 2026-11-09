extern int printf(const char *, ...);
typedef unsigned long long U;
U mx(U u,U v,int n){U d[16][16]={0};
 for(int i=n;i>=0;--i)for(int j=n;j>=0;--j){
  if(i==n){d[i][j]=v&((1ULL<<(n-j))-1);continue;}
  if(j==n){d[i][j]=u&((1ULL<<(n-i))-1);continue;}
  int a=(u>>(n-i-1))&1,b=(v>>(n-j-1))&1,len=2*n-i-j;
  U x=d[i+1][j]|((U)a<<(len-1)),y=d[i][j+1]|((U)b<<(len-1));
  d[i][j]=a==b?(x>y?x:y):(a==0?x:y);
 }return d[0][0];}
int run(int n){U count=1ULL<<n,pairs=0,prior=0;int any=0;
 for(U w=0;w<count;++w){U square=mx(w,w,n);if(any&&prior>=square){printf("FAIL prior n=%d w=%llu\n",n,(unsigned long long)w);return 1;}
  for(U x=0;x<w;++x){U z=mx(x,w,n);++pairs;if(z>=square){printf("FAIL n=%d x=%llu w=%llu max=%llu square=%llu\n",n,(unsigned long long)x,(unsigned long long)w,(unsigned long long)z,(unsigned long long)square);return 1;}if(!any||z>prior)prior=z;any=1;}
  if(!any||square>prior)prior=square;any=1;
 }
 printf("n=%d words=%llu unordered_distinct_pairs=%llu strict_leading_square_criterion=PASS\n",n,(unsigned long long)count,(unsigned long long)pairs);
 return 0;
}
