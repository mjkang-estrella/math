#include <bits/stdc++.h>
using namespace std;
long long cnt[2][4];int p[30],n,pat;bool used[30];
bool cyc(int allowed){bool seen[30]={};for(int i=0;i<n;i++)if(!seen[i]){int j=i,k=0;do{seen[j]=true;j=p[j];k++;}while(j!=i);if(k>3||(!(allowed&2)&&k==2))return false;}return true;}
int pattern(int a,int b,int c){if(a<b&&b<c)return 0;if(a<c&&c<b)return 1;if(c<b&&b<a)return 2;if(c<a&&a<b)return 3;return 4;}
void rec(int k){if(k==n){if(cyc(2))cnt[1][pat]++;if(cyc(0))cnt[0][pat]++;return;}for(int v=0;v<n;v++)if(!used[v]){bool ok=true;for(int i=0;i<k&&ok;i++)for(int j=i+1;j<k;j++)if(pattern(p[i],p[j],v)==pat){ok=false;break;}if(ok){p[k]=v;used[v]=true;rec(k+1);used[v]=false;}}}
int main(int argc,char**argv){int N=argc>1?atoi(argv[1]):14;for(n=1;n<=N;n++){memset(cnt,0,sizeof cnt);for(pat=0;pat<4;pat++)rec(0);cout<<n;for(int a=0;a<2;a++)for(int b=0;b<4;b++)cout<<' '<<cnt[a][b];cout<<endl;}}
