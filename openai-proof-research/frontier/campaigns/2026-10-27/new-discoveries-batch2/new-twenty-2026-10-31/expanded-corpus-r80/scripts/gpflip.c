extern int scanf(const char *, ...); extern int printf(const char *, ...); extern int fflush(void *); extern void *stdout;
int a[64],b[64];
int gp(int n,int m,unsigned mask){
 int d[12][12];for(int i=0;i<n;i++)for(int j=0;j<n;j++)d[i][j]=i==j?0:99;
 for(int k=0;k<m;k++){int u=a[k],v=b[k];if(mask>>k&1)d[v][u]=1;else d[u][v]=1;}
 for(int k=0;k<n;k++)for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(d[i][j]>d[i][k]+d[k][j])d[i][j]=d[i][k]+d[k][j];
 unsigned bad[220];int nb=0;
 for(int u=0;u<n;u++)for(int v=u+1;v<n;v++)for(int w=v+1;w<n;w++){
 int t[3]={u,v,w},no=0;for(int i=0;i<3;i++)for(int j=0;j<3;j++)if(i!=j){int k=3-i-j;if(d[t[i]][t[k]]<99&&d[t[i]][t[k]]==d[t[i]][t[j]]+d[t[j]][t[k]])no=1;}
 if(no)bad[nb++]=(1u<<u)|(1u<<v)|(1u<<w);
 }
 int best=0;for(unsigned s=0;s<(1u<<n);s++){int pc=__builtin_popcount(s);if(pc<=best)continue;int ok=1;for(int k=0;k<nb;k++)if((s&bad[k])==bad[k]){ok=0;break;}if(ok)best=pc;}return best;
}
int main(){int id,n,m;while(scanf("%d %d %d",&id,&n,&m)==3){for(int k=0;k<m;k++)scanf("%d %d",&a[k],&b[k]);int values[32768];for(unsigned s=0;s<(1u<<m);s++)values[s]=gp(n,m,s);for(unsigned s=0;s<(1u<<m);s++)for(int k=0;k<m;k++)if(values[s]+1<values[s^(1u<<k)]){printf("graph %d n %d m %d mask %u edge %d gp_before %d gp_after %d\n",id,n,m,s,k,values[s],values[s^(1u<<k)]);return 0;}}return 1;}
