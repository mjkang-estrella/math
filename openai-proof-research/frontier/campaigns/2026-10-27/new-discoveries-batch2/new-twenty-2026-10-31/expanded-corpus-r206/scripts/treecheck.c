typedef unsigned long long U;
U paths[32][32];int ds[32][32],n;U *adj;
void build(int root,int v,int p,int d,U path){ds[root][v]=d;paths[root][v]=path;U nbr=adj[v];for(int w=0;w<n;w++)if(w!=p&&(nbr>>w&1))build(root,w,v,d+1,path|(p<0?0:1ULL<<v));}
int dominates(U s){for(int u=0;u<n;u++)if(!(s>>u&1)){U sum=0;for(int v=0;v<n;v++)if((s>>v&1)&&!(paths[u][v]&s))sum+=1ULL<<(n+1-ds[u][v]);if(sum<(1ULL<<n))return 0;}return 1;}
U check(int N,U *a){n=N;adj=a;for(int u=0;u<n;u++)build(u,u,-1,0,0);for(int k=1;k<(n+2)/3;k++){U s=(1ULL<<k)-1,lim=1ULL<<n;while(s<lim){if(dominates(s))return s;U c=s&-s,r=s+c;s=(((r^s)>>2)/c)|r;}}return 0;}
