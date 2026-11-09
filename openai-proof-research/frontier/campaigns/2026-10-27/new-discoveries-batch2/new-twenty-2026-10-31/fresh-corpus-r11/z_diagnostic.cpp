#include <vector>
#include <iostream>
#include <chrono>
int main(){ for(int g=14;g<=15;g++){ int n=(1<<g)+1; bool ok=true; for(int p=2;p*p<=n;p++){bool prime=true;for(int q=2;q*q<=p;q++)if(p%q==0)prime=false;if(!prime)continue;std::vector<unsigned char>a(n);for(int j=1;j<=n;j++){int k=j;while(k%p==0){a[j-1]++;k/=p;}}for(int len=n;len>1;len--)for(int j=0;j<len-1;j++){int d=int(a[j])-int(a[j+1]);a[j]=d<0?-d:d;}int t=n,v=0;while(t%p==0){v++;t/=p;}if(a[0]!=(v%2)){ok=false;std::cout<<"FAIL "<<g<<" "<<p<<" "<<int(a[0])<<" "<<v%2<<std::endl;}}std::cout<<"g "<<g<<" small-prime-valuations match "<<ok<<std::endl;}}
