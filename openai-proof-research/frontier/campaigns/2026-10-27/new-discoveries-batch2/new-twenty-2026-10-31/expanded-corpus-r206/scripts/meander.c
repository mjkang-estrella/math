extern int printf(const char *, ...);
extern int atoi(const char *);
unsigned char ps[210000][12],qs[210000][12];int a[12],cnt[210000],N,count;
void gen(int at,int mx){if(at==N){for(int i=0;i<N;i++)for(int j=i+1;j<N;j++)if(a[i]!=a[j])for(int k=j+1;k<N;k++)if(a[k]==a[i])for(int l=k+1;l<N;l++)if(a[l]==a[j])return;for(int i=0;i<N;i++){int j=(i+1)%N;while(a[i]!=a[j])j=(j+1)%N;ps[count][i]=j;qs[count][j]=i;}count++;return;}for(int b=0;b<=mx+1;b++){a[at]=b;gen(at+1,b>mx?b:mx);}}
int main(int argc,char**argv){N=atoi(argv[1]);gen(1,0);for(int i=0;i<count;i++)for(int j=i+1;j<count;j++){int x=ps[i][qs[j][0]],k=1;while(x){x=ps[i][qs[j][x]];k++;}if(k==N){cnt[i]++;cnt[j]++;}}int best=0,mult=0,r=-1;for(int i=0;i<count;i++){int rb=1;for(int j=0;j<N;j++)if(ps[i][j]!=N-1-j)rb=0;if(rb)r=cnt[i];if(cnt[i]>best){best=cnt[i];mult=0;}if(cnt[i]==best)mult++;}printf("n=%d partitions=%d pairs=%lld maximum=%d maximizers=%d rainbow=%d\n",N,count,(long long)count*(count-1)/2,best,mult,r);return 0;}
