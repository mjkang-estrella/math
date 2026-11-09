extern int printf(const char*,...); extern int puts(const char*); extern int atoi(const char*); extern void *memset(void*,int,unsigned long); extern int fflush(void*); extern void *stdout;
long long cnt[2][4];int p[30],n,pat,used[30];
int cyc(int allowed){int seen[30]={0};for(int i=0;i<n;i++)if(!seen[i]){int j=i,k=0;do{seen[j]=1;j=p[j];k++;}while(j!=i);if(k>3||(!allowed&&k==2))return 0;}return 1;}
int pattern(int a,int b,int c){if(a<b&&b<c)return 0;if(a<c&&c<b)return 1;if(c<b&&b<a)return 2;if(c<a&&a<b)return 3;return 4;}
void rec(int k){if(k==n){if(cyc(1))cnt[1][pat]++;if(cyc(0))cnt[0][pat]++;return;}for(int v=0;v<n;v++)if(!used[v]){int ok=1;for(int i=0;i<k&&ok;i++)for(int j=i+1;j<k;j++)if(pattern(p[i],p[j],v)==pat){ok=0;break;}if(ok){p[k]=v;used[v]=1;rec(k+1);used[v]=0;}}}
int main(int argc,char**argv){n=atoi(argv[1]);pat=atoi(argv[2]);rec(0);printf("n %d pattern %d count13 %lld count123 %lld\n",n,pat,cnt[0][pat],cnt[1][pat]);}
