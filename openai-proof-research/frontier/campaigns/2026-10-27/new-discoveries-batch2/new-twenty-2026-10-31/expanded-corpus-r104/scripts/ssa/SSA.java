import java.util.*;
// m-SSA generating set local search. Alphabet A=0,C=1,G=2,T=3; complement x->3-x.
public class SSA {
  static int m, N; static int[] rc;
  static double rho(boolean[] in, double[] v0) {
    double[] v = new double[N]; for (int i=0;i<N;i++) v[i]= in[i]? (v0!=null? v0[i]+1e-9:1):0;
    double lam=0;
    for (int it=0; it<3000; it++) {
      double[] w=new double[N]; double s=0;
      for (int x=0;x<N;x++) if (in[x] && v[x]>0) { int b=(x*4)%N; for(int c=0;c<4;c++){int y=b+c; if(in[y]) w[y]+=v[x];}}
      // average two steps to avoid periodicity issues
      for (int i=0;i<N;i++){ w[i]=0.5*w[i]+0.5*v[i]; s+=w[i]; }
      double nl = s; for(int i=0;i<N;i++) w[i]/=s;
      double tot=0; for(int i=0;i<N;i++) tot+=v[i];
      if (Math.abs(nl/tot - lam) < 1e-13 && it>50) { lam = nl/tot; v=w; break; }
      lam = nl/tot; v=w;
    }
    if (v0!=null) System.arraycopy(v,0,v0,0,N);
    return 2*lam-1; // undo lazy averaging: eigen of (A+I)/2 -> (rho+1)/2
  }
  static int rcOf(int x){int r=0; for(int i=0;i<m;i++){int d=x%4; x/=4; r=r*4+(3-d);} return r;}
  public static void main(String[] a){
    m=Integer.parseInt(a[0]); N=1<<(2*m); long seed=Long.parseLong(a[1]); int iters=Integer.parseInt(a[2]);
    rc=new int[N]; for(int x=0;x<N;x++) rc[x]=rcOf(x);
    boolean[] tc=new boolean[N];
    for(int x=0;x<N;x++){int y=x,o=0; for(int i=0;i<m;i++){ if((y%4)%2==1) o++; y/=4;} tc[x]= 2*o>m; }
    double rtc=rho(tc,null);
    System.out.printf("m=%d TC rho=%.10f rate=%.6f%n", m, rtc, Math.log(rtc)/Math.log(2));
    Random R=new Random(seed);
    boolean[] cur=tc.clone(); int mode=Integer.parseInt(a[3]); double T0=Double.parseDouble(a[4]);
    int[] bnd=new int[N]; int nb=0; for(int x=0;x<N;x++){int y=x,o=0; for(int i=0;i<m;i++){ if((y%4)%2==1) o++; y/=4;} if(o==(m+1)/2||o==(m-1)/2) bnd[nb++]=x;}
    if(mode==2){ for(int i=0;i<nb;i++){int x=bnd[i]; if(x<rc[x] && R.nextDouble()<0.5){ boolean b=cur[x]; cur[x]=!b; cur[rc[x]]=b; }} }
    if(mode==1){ for(int x=0;x<N;x++) if(x<rc[x]){ boolean b=R.nextBoolean(); cur[x]=b; cur[rc[x]]=!b; } } double[] vec=new double[N]; double rcur=rho(cur,vec); System.out.println("start rho "+rcur); double best=rcur; boolean[] bestS=cur.clone();
    double T=T0;
    for(int it=0; it<iters; it++){
      int x=(mode>=2)? bnd[R.nextInt(nb)] : R.nextInt(N); if (x==rc[x]) continue;
      boolean[] nx=cur.clone(); boolean had=nx[x]; nx[x]=!had; nx[rc[x]]=had;
      double[] v2=vec.clone(); double r2=rho(nx,v2);
      if (r2>rcur || R.nextDouble()<Math.exp((r2-rcur)/T)) { cur=nx; rcur=r2; vec=v2; }
      if (rcur>best+1e-12){best=rcur; bestS=cur.clone(); System.out.printf("it=%d best=%.10f rate=%.6f%n",it,best,Math.log(best)/Math.log(2));}
      T*=Math.pow(1e-4,1.0/iters);
    }
    StringBuilder sb=new StringBuilder(); String al="ACGT";
    for(int x=0;x<N;x++) if(bestS[x]){ int y=x; char[] cs=new char[m]; for(int i=m-1;i>=0;i--){cs[i]=al.charAt(y%4); y/=4;} sb.append(new String(cs)).append(' ');}
    System.out.println("BEST "+best); System.out.println("SET "+sb);
  }
}
