#include <algorithm>
#include <iostream>
#include <vector>
#include <functional>
using namespace std;
vector<long long> counts(vector<int> sh){int m=sh.size(),N=0;for(int x:sh)N+=x;vector<vector<int>> a(m);vector<long long> c(N*N+1);function<void(int)> rec=[&](int v){if(v>N){int inv=0;for(int r=0;r<m;r++)for(int s=r+1;s<m;s++)for(int j=0;j<min(sh[r],sh[s]);j++){int small=a[r][j]<a[s][j]?r:s,large=small==r?s:r;if(j+1>=sh[small]||j+1>=sh[large]) inv+=small>large;else inv+=a[small][j+1]>a[large][j+1];}c[inv]++;return;}for(int r=0;r<m;r++)if(a[r].size()<sh[r]){a[r].push_back(v);rec(v+1);a[r].pop_back();}};rec(1);while(c.size()>1&&c.back()==0)c.pop_back();return c;}
int main(){for(int m=2;m<=8;m++)for(int n=1;n<=8;n++){if(m*n>14)continue;long double cnt=1;for(int k=1;k<=m*n;k++)cnt*=k;for(int r=0;r<m;r++)for(int k=1;k<=n;k++)cnt/=k;if(cnt>20000000)continue;vector<int>s(m,n),t=s;t[0]++;t.back()--;auto a=counts(s),b=counts(t);bool ok=true;for(int i=n*(m-2)*(m-1)/2+1;i<(int)a.size();i++){long long z=i-m+1>=0&&i-m+1<b.size()?b[i-m+1]:0;if(a[i]!=z){ok=false;cout<<"FAIL "<<m<<" "<<n<<" "<<i<<" "<<a[i]<<" "<<z<<endl;}}cout<<"m "<<m<<" n "<<n<<" count "<<(long long)(cnt+.5)<<" holds "<<ok<<" A";for(auto z:a)cout<<" "<<z;cout<<" B";for(auto z:b)cout<<" "<<z;cout<<endl;}}
