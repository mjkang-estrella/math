extern int printf(const char*,...);extern int atoi(const char*);extern int fflush(void*);extern void*calloc(unsigned long,unsigned long);extern void*malloc(unsigned long);extern void free(void*);typedef unsigned long long U;typedef unsigned short S;
#define MAX 6000000
#define HS 16777216
S (*cur)[12],(*next)[12];int*ht;int ell,T;
int ab(int x){return x<0?-x:x;}
int h0(int id){int x=id/128-16,y=id%128-ell-16;if(x<0)return ab(x)+ab(y);if(x<ell)return ab(x+y);return ab(y+ell-1)+ab(x-ell+1);}
int height(S*c,int id,int t){int h=h0(id);for(int j=0;j<t;j++)if(c[j]==id)h+=2;return h;}
int main(int argc,char**argv){ell=atoi(argv[1]);T=atoi(argv[2]);cur=calloc(MAX,24);next=calloc(MAX,24);ht=calloc(HS,4);int nc=1;printf("ell=%d n=0 count=1\n",ell);for(int t=0;t<T;t++){for(int i=0;i<HS;i++)ht[i]=0;int nn=0;for(int i=0;i<nc;i++){S*c=cur[i];int cand[100],cn=0;for(int x=0;x<ell;x++)cand[cn++]=(x+16)*128+(-x+ell+16);for(int j=0;j<t;j++){int p=c[j];int adj[5]={p,p-128,p+128,p-1,p+1};for(int k=0;k<5;k++){int z=adj[k],found=0;for(int u=0;u<cn;u++)if(cand[u]==z)found=1;if(!found)cand[cn++]=z;}}
for(int j=0;j<cn;j++){int p=cand[j],h=height(c,p,t);if(height(c,p-128,t)!=h+1||height(c,p+128,t)!=h+1||height(c,p-1,t)!=h+1||height(c,p+1,t)!=h+1)continue;S b[12]={0};int k=0;while(k<t&&c[k]<=p){b[k]=c[k];k++;}b[k]=p;for(int u=k;u<t;u++)b[u+1]=c[u];U hash=138;for(int u=0;u<=t;u++)hash=(hash^b[u])*1099511628211ULL;int pos=hash&(HS-1),found=0;while(ht[pos]){int ix=ht[pos]-1,eq=1;for(int u=0;u<=t;u++)if(next[ix][u]!=b[u])eq=0;if(eq){found=1;break;}pos=(pos+1)&(HS-1);}if(!found){if(nn==MAX){printf("CAP ell=%d completed_n=%d completed_count=%d\n",ell,t,nc);return 2;}for(int u=0;u<12;u++)next[nn][u]=b[u];ht[pos]=++nn;}}}
S(*tmp)[12]=cur;cur=next;next=tmp;nc=nn;printf("ell=%d n=%d count=%d\n",ell,t+1,nc);fflush(0);}free(cur);free(next);free(ht);}
