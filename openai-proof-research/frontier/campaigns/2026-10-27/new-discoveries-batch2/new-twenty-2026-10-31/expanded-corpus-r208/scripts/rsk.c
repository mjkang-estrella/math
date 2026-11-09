extern int printf(const char*,...);extern int fflush(void*);
static int p[15],n; static long long total,trace,zero;
static void one(){int a[15][15]={0},len[15]={0},qcol[15]={0},pcol[15]={0},r,c,x,y,i,j,sign=1;
for(i=0;i<n;i++){x=p[i];r=0;for(;;){c=0;while(c<len[r]&&a[r][c]<x)c++;if(c==len[r]){a[r][len[r]++]=x;qcol[i]=c;break;}y=a[r][c];a[r][c]=x;x=y;r++;}}
for(r=0;r<n;r++)for(c=0;c<len[r];c++)pcol[a[r][c]]=c;
for(i=0;i<n;i++)if(pcol[p[i]]!=qcol[i]){total++;zero++;return;}
for(i=0;i<n;i++)for(j=i+1;j<n;j++)if(qcol[i]==qcol[j]&&p[i]>p[j])sign=-sign;
total++;trace+=sign;}
static void gen(int k,int bits){if(k==n){one();return;}for(int i=0;i<n;i++)if(!(bits>>i&1)){p[k]=i;gen(k+1,bits|(1<<i));}}
int main(){for(n=1;n<=12;n++){total=trace=zero=0;gen(0,0);printf("n=%d permutations=%lld trace=%lld zero=%lld\n",n,total,trace,zero);fflush((void*)0);}return 0;}
