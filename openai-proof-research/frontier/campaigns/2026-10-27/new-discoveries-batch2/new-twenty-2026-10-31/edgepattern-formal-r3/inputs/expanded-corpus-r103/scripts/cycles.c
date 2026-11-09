typedef unsigned long long uint64_t;
extern void *calloc(unsigned long,unsigned long);
extern void free(void *);
uint64_t *counts(int n,int d){
 uint64_t *out=calloc(1<<n,8);
 for(int s=0;s<n;s++){
  int m=n-s;uint64_t *dp=calloc((1<<m)*m,8);dp[m]=1;int to[24]={0},close[24]={0};
  for(int a=0;a<m;a++)for(int b=0;b<m;b++){
   int x=a+s+1,y=b+s+1,ok=d?(x%2?x<=y:x>=y):(x<=y||(!(x%2)&&(y%2)));
   if(ok){if(b)to[a]|=1<<b;else close[a]=1;}
  }
  for(int mask=1;mask<(1<<m);mask+=2)for(int a=0;a<m;a++){
   uint64_t c=dp[mask*m+a];if(!c)continue;
   if(close[a])out[mask<<s]+=c;
   int todo=to[a]&~mask;while(todo){int b=__builtin_ctz(todo);todo&=todo-1;dp[(mask|(1<<b))*m+b]+=c;}
  }
  free(dp);
 }
 return out;
}
