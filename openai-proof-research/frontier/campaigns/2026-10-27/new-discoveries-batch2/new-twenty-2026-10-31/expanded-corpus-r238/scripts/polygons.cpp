#include <bits/stdc++.h>
using namespace std;using P=pair<long long,long long>;mt19937 rng(238);
long long orient(P a,P b,P c){return (b.first-a.first)*(c.second-a.second)-(b.second-a.second)*(c.first-a.first);}
bool cross(P a,P b,P c,P d){auto x=orient(a,b,c),y=orient(a,b,d),z=orient(c,d,a),t=orient(c,d,b);return (x<0)!=(y<0)&&(z<0)!=(t<0)&&x&&y&&z&&t;}
bool simple(vector<P>const&p){int n=p.size();for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)if((i+1)%n!=j&&(j+1)%n!=i&&cross(p[i],p[(i+1)%n],p[j],p[(j+1)%n]))return false;return true;}
bool gp(vector<P>const&a,vector<P>const&b){vector<P> p=a;p.insert(p.end(),b.begin(),b.end());for(int i=0;i<(int)p.size();i++)for(int j=i+1;j<(int)p.size();j++)for(int k=j+1;k<(int)p.size();k++)if(!orient(p[i],p[j],p[k]))return false;return true;}
int score(vector<P>const&a,vector<P>const&b){int s=0;for(int i=0;i<(int)a.size();i++)for(int j=0;j<(int)b.size();j++)s+=cross(a[i],a[(i+1)%a.size()],b[j],b[(j+1)%b.size()]);return s;}
vector<P> init(int n){vector<P> p;for(int i=0;i<n;i++)p.push_back({(int)(rng()%2001)-1000,(int)(rng()%2001)-1000});double x=0,y=0;for(auto z:p)x+=z.first,y+=z.second;x/=n;y/=n;sort(p.begin(),p.end(),[&](P a,P b){return atan2(a.second-y,a.first-x)<atan2(b.second-y,b.first-x);});return p;}
int main(int argc,char**argv){int n=atoi(argv[1]),m=atoi(argv[2]);long long loops=atoll(argv[3]),valid=0;int best=-1;vector<P>ba,bb,a,b;int s=0;for(long long it=0;it<loops;it++){
 if(it%10000==0){do{a=init(n);b=init(m);}while(!simple(a)||!simple(b)||!gp(a,b));s=score(a,b);}
 auto aa=a,ab=b;auto &p=(rng()%2)?aa:ab;int z=rng()%p.size(),mtype=rng()%3;
 if(mtype==0){int w=rng()%p.size();if(z>w)swap(z,w);reverse(p.begin()+z,p.begin()+w+1);}
 else if(mtype==1){p[z].first+=(int)(rng()%301)-150;p[z].second+=(int)(rng()%301)-150;}
 else p[z]={(int)(rng()%2001)-1000,(int)(rng()%2001)-1000};
 if(!simple(aa)||!simple(ab)||!gp(aa,ab))continue;valid++;int t=score(aa,ab);double temp=2.5*(1-(it%10000)/10000.0)+.05;if(t>=s||generate_canonical<double,32>(rng)<exp((t-s)/temp)){a=aa;b=ab;s=t;}
 if(t>best){best=t;ba=aa;bb=ab;}
 if(best>n*m-n-m+3)break;
 }
 cout<<"{\"m\":"<<n<<",\"n\":"<<m<<",\"proposed_iterations\":"<<loops<<",\"valid_proposals\":"<<valid<<",\"best_crossings\":"<<best<<",\"conjectured_bound\":"<<n*m-n-m+3<<",\"seed\":238,\"P\":[";for(int i=0;i<n;i++)cout<<(i?",":"")<<"["<<ba[i].first<<","<<ba[i].second<<"]";cout<<"],\"Q\":[";for(int i=0;i<m;i++)cout<<(i?",":"")<<"["<<bb[i].first<<","<<bb[i].second<<"]";cout<<"]}"<<endl;
}
