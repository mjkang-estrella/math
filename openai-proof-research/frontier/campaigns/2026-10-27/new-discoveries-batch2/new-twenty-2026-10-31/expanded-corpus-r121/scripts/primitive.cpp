#include <bits/stdc++.h>
using namespace std;
long long checked=0,valid=0,fail=0; int p,n;vector<int>v;
int reps(){int total=0;for(int k=1;k<p;k++){vector<int>u(n);int sum=0,sq=0;for(int i=0;i<n;i++){int a=k*v[i]%p;if(a>p/2)a-=p;u[i]=a;sum+=a;sq+=a*a;}if(sq>p*p)continue;
 auto ok=[&](int s,int q){if(s==p&&q==p*p)total++;};ok(sum,sq);
 for(int i=0;i<n;i++){int di=u[i]>0?-p:p;int qi=2*di*u[i]+p*p;ok(sum+di,sq+qi);
 for(int j=i+1;j<n;j++){int dj=u[j]>0?-p:p;int qj=2*dj*u[j]+p*p;ok(sum+di+dj,sq+qi+qj);
 for(int l=j+1;l<n;l++){int dl=u[l]>0?-p:p;int ql=2*dl*u[l]+p*p;ok(sum+di+dj+dl,sq+qi+qj+ql);}}}}
 return total;}
void test(){checked++;int s=0,q=0;for(int a:v){s+=a;q+=a*a;}if(s%p||q%p)return;valid++;int r=reps();if((n<=8&&r!=n)||(n>=2*p+1&&r==n)){fail++;cout<<"FAIL p="<<p<<" n="<<n<<" r="<<r<<" v=";for(int a:v)cout<<a<<",";cout<<endl;}}
void gen(int i,int lo){if(i==n){test();return;}for(int a=lo;a<p;a++){v[i]=a;gen(i+1,a);}}
int main(int argc,char**argv){p=atoi(argv[1]);n=atoi(argv[2]);v.resize(n);gen(0,1);cout<<"p="<<p<<" n="<<n<<" multisets="<<checked<<" isotropic="<<valid<<" failures="<<fail<<endl;}
