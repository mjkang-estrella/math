import java.util.*;
// Structured samples of surjective binary CA with larger radius: permutive rules and compositions of surjective rules.
public class CAsample {
  static boolean surj(int r, boolean[] f){ int S=1<<r; int V=S*S; boolean[] fw=new boolean[V]; int[] q=new int[V]; int h=0,t=0;
    for(int u=0;u<S;u++){ int wu=u, wv=u|(1<<r); if(f[wu]!=f[wv]) continue;
      int id=(wu>>1)*S+(wv>>1); if(!fw[id]){fw[id]=true;q[t++]=id;} id=(wv>>1)*S+(wu>>1); if(!fw[id]){fw[id]=true;q[t++]=id;} }
    while(h<t){int id=q[h++]; int u=id/S,v=id%S; if(u==v) return false;
      for(int a=0;a<2;a++)for(int b=0;b<2;b++){int wu=u|(a<<r), wv=v|(b<<r); if(f[wu]!=f[wv]) continue; int nid=(wu>>1)*S+(wv>>1); if(!fw[nid]){fw[nid]=true;q[t++]=nid;} }}
    return true; }
  static boolean[] compose(int r1, boolean[] f1, int r2, boolean[] f2){ // F2 after F1
    int r=r1+r2; boolean[] f=new boolean[1<<(r+1)];
    for(int w=0;w<(1<<(r+1));w++){ int mid=0; for(int i=0;i<=r2;i++){ int sub=(w>>i)&((1<<(r1+1))-1); if(f1[sub]) mid|=1<<i; } f[w]=f2[mid]; }
    return f; }
  static String check(int r, boolean[] f){ long[] N=new long[r+2], id=new long[r+2];
    for(int w=0;w<(1<<(r+1));w++){int k=Integer.bitCount(w); if(f[w]) N[k]++; if((w&1)==1) id[k]++;}
    long s1=0,s2=0; for(int n=0;n<=r+1;n++){s1+=N[n];s2+=id[n]; if(s1<s2) return Arrays.toString(N);} return null; }
  public static void main(String[] a){
    Random R=new Random(Long.parseLong(a[0])); long tested=0, viol=0;
    long t0=System.currentTimeMillis();
    // base pool: all surjective rules r<=3
    List<boolean[]>[] pool=new List[4];
    for(int r=1;r<=3;r++){ pool[r]=new ArrayList<>(); int W=1<<(r+1); for(long tt=0;tt<(1L<<W);tt++){ boolean[] f=new boolean[W]; for(int w=0;w<W;w++) f[w]=((tt>>w)&1)==1; if(surj(r,f)) pool[r].add(f);} }
    while(System.currentTimeMillis()-t0<100000){
      int mode=R.nextInt(3); int r; boolean[] f;
      if(mode==0){ r=5+R.nextInt(8); f=new boolean[1<<(r+1)]; boolean left=R.nextBoolean(); boolean[] g=new boolean[1<<r]; for(int i=0;i<g.length;i++) g[i]=R.nextBoolean();
        for(int w=0;w<f.length;w++){ if(left) f[w]=((w&1)==1)^g[w>>1]; else f[w]=(((w>>r)&1)==1)^g[w&((1<<r)-1)]; } }
      else { int r1=1+R.nextInt(3), r2=1+R.nextInt(3); f=compose(r1,pool[r1].get(R.nextInt(pool[r1].size())),r2,pool[r2].get(R.nextInt(pool[r2].size()))); r=r1+r2;
        if(mode==2 && r<=9){ int r3=1+R.nextInt(3); f=compose(r,f,r3,pool[r3].get(R.nextInt(pool[r3].size()))); r+=r3; } }
      tested++; String c=check(r,f); if(c!=null){ viol++; if(viol<10) System.out.println("VIOLATION r="+r+" N="+c+" surj="+surj(r,f)); }
    }
    System.out.println("tested="+tested+" violations="+viol);
  }
}
