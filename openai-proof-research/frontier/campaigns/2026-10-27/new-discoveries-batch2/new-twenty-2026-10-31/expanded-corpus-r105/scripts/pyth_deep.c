extern int printf(const char*,...);extern double sqrt(double);
int check(long long q){long long r=(long long)sqrt((double)q);return r*r==q||(r+1)*(r+1)==q;}
int witness(int g,int h){for(int m=2;m<=100;m++)for(int n=1;n<m;n++){int a=m*m-n*n,b=2*m*n;for(int sw=0;sw<2;sw++)for(int sign=-1;sign<=1;sign+=2){int x=sw?b:a,y=sign*(sw?a:b);for(int k=-500;k<=500;k++){if(!k)continue;long long u=g-(long long)k*x,v=h-(long long)k*y;if(u&&v&&check(u*u+v*v)){printf("%d %d via %d %d times %d residual %lld %lld\n",g,h,x,y,k,u,v);return 1;}}}}return 0;}
