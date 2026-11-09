extern int printf(const char*,...);extern int fflush(void*);
int main(){for(int n=3;n<=7;n++){unsigned long count=0,active=0;int bestv=-99,beste=-99,wv=0,we=0;
for(unsigned mask=0;mask<(1u<<(n*(n-1)/2));mask++){
 int adj[8]={0},deg[8]={0},edges[28][2],m=0,b=0,d[8][8];
 for(int i=0;i<n;i++)for(int j=0;j<n;j++)d[i][j]=(i==j?0:99);
 for(int i=0;i<n;i++)for(int j=i+1;j<n;j++,b++)if(mask>>b&1){adj[i]|=1<<j;adj[j]|=1<<i;deg[i]++;deg[j]++;d[i][j]=d[j][i]=1;edges[m][0]=i;edges[m++][1]=j;}
 int seen=1,last=0;while(seen!=last){last=seen;for(int i=0;i<n;i++)if(seen>>i&1)seen|=adj[i];}if(seen!=(1<<n)-1)continue;
 count++;int c=m-n+1;if(c<2)continue;
 int L=0;for(int v=0;v<n;v++)if(deg[v]>=3){int legs=0;for(int a=0;a<n;a++)if(adj[v]>>a&1){int prev=v,u=a;while(deg[u]==2){int next=__builtin_ctz((unsigned)(adj[u]&~(1<<prev)));prev=u;u=next;}if(deg[u]==1)legs++;}if(legs>1)L+=legs-1;}
 int Z=n;for(int s=1;s<(1<<n);s++)if(__builtin_popcount((unsigned)s)<Z){int t=s,old=0;while(t!=old){old=t;for(int i=0;i<n;i++)if(t>>i&1){unsigned w=adj[i]&~t;if(w&&!(w&(w-1)))t|=w;}}if(t==(1<<n)-1)Z=__builtin_popcount((unsigned)s);}
 if(L+2*c>=n-1&&Z+c>=n-1)continue;active++;
 for(int z=0;z<n;z++)for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(d[i][z]+d[z][j]<d[i][j])d[i][j]=d[i][z]+d[z][j];
 int vd=n,ed=n;for(int s=1;s<(1<<n);s++){int sz=__builtin_popcount((unsigned)s);if(sz<vd){int ok=1;for(int i=0;i<n&&ok;i++)for(int j=i+1;j<n&&ok;j++){int hit=0;for(int v=0;v<n;v++)if((s>>v&1)&&d[v][i]!=d[v][j]){hit=1;break;}if(!hit)ok=0;}if(ok)vd=sz;}
 if(sz<ed){int ok=1;for(int i=0;i<m&&ok;i++)for(int j=i+1;j<m&&ok;j++){int hit=0;for(int v=0;v<n;v++)if(s>>v&1){int a=d[v][edges[i][0]],a1=d[v][edges[i][1]],bb=d[v][edges[j][0]],b1=d[v][edges[j][1]];if((a<a1?a:a1)!=(bb<b1?bb:b1)){hit=1;break;}}if(!hit)ok=0;}if(ok)ed=sz;}}
 if(vd-L-2*c>bestv){bestv=vd-L-2*c;wv=mask;}if(ed-Z-c>beste){beste=ed-Z-c;we=mask;}
 if(vd>L+2*c||ed>Z+c)printf("FAIL n=%d mask=%u dim=%d edim=%d L=%d Z=%d c=%d\n",n,mask,vd,ed,L,Z,c);
}
printf("n=%d connected_labelled=%lu explicit_checks=%lu max_checked_vertex_gap=%d mask=%d max_checked_edge_gap=%d mask=%d\n",n,count,active,bestv,wv,beste,we);fflush(0);
}}
