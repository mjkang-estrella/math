#include <algorithm>
#include <vector>
#include <iostream>
#include <fstream>
using namespace std;
int main(int argc,char**argv){int n=stoi(argv[1]),first=argc>2?stoi(argv[2]):0;vector<int>a(n),p(n+1);for(int i=0;i<n;i++)a[i]=i+1;vector<long long>cnt((1<<n)*(n+2));long long total=0;
do{if(first&&a[0]!=first)continue;int s=0,d=1;for(int i=0;i<n;i++)p[a[i]]=i;for(int i=1;i<n-1;i++)if(a[i]>a[i-1]&&a[i]>a[i+1])s|=1<<(a[i]-1);for(int i=1;i<n;i++)d+=p[i]>p[i+1];cnt[s*(n+2)+d]++;total++;}while(next_permutation(a.begin(),a.end()));
cout<<"n "<<n<<" first "<<first<<" permutations "<<total<<endl;int sets=0;for(int s=0;s<(1<<n);s++){vector<long long>v(n+2);for(int d=0;d<=n+1;d++)v[d]=cnt[s*(n+2)+d];if(!count_if(v.begin(),v.end(),[](long long x){return x!=0;}))continue;sets++;for(int j=0;j<=(n+1)/2;j++){long long g=v[j];if(g<0){cout<<"NEGATIVE mask "<<s<<" gamma_index "<<j<<" value "<<g<<endl;return 2;}long long b=1;int m=n+1-2*j;for(int k=0;k<=m;k++){v[j+k]-=g*b;if(k<m)b=b*(m-k)/(k+1);}}for(auto t:v)if(t){cout<<"NONSYMMETRIC "<<s<<endl;return 3;}}
cout<<"all nonnegative sets "<<sets<<endl;}
