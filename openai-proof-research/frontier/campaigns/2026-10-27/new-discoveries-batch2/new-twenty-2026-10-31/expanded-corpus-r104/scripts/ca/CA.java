import java.util.*;
// Binary CA, one-sided radius r: F(x)_i = f(x_i..x_{i+r}). Word w in {0,1}^{r+1} encoded with bit j = cell j.
public class CA {
  static int r;
  // surjective iff pair graph has no diamond (off-diagonal vertex reachable from diagonal and coreachable to diagonal)
  static boolean surj(long tt){
    int S=1<<r; int V=S*S; // state = last r cells
    boolean[] fw=new boolean[V], bw=new boolean[V];
    ArrayDeque<Integer> q=new ArrayDeque<>();
    // forward from diagonal via edges leaving diagonal
    for(int u=0;u<S;u++) for(int a=0;a<2;a++) for(int b=0;b<2;b++){ if(a==b) continue;
      int wu=u|(a<<r), wv=u|(b<<r); if(((tt>>wu)&1)!=((tt>>wv)&1)) continue;
      int nu=wu>>1, nv=wv>>1; int id=nu*S+nv; if(!fw[id]){fw[id]=true;q.add(id);} }
    while(!q.isEmpty()){int id=q.poll(); int u=id/S,v=id%S; if(u==v) return false;
      for(int a=0;a<2;a++)for(int b=0;b<2;b++){int wu=u|(a<<r), wv=v|(b<<r); if(((tt>>wu)&1)!=((tt>>wv)&1)) continue;
        int nid=(wu>>1)*S+(wv>>1); if(!fw[nid]){fw[nid]=true;q.add(nid);} }}
    return true; // no path from diagonal-departure back to diagonal => no diamond
  }
  public static void main(String[] a){
    r=Integer.parseInt(a[0]); int W=1<<(r+1);
    long[] binom=new long[r+2]; // id: f(w)=w_0 -> N(id,k)=C(r,k-1)
    int[] pc=new int[W]; for(int w=0;w<W;w++) pc[w]=Integer.bitCount(w);
    long[] idN=new long[r+2]; for(int w=0;w<W;w++) if((w&1)==1) idN[pc[w]]++;
    long total=1L<<W, surjCount=0, viol=0, balanced=0;
    for(long tt=0; tt<total; tt++){
      if(Long.bitCount(tt & (total==(1L<<63)?-1L:(total-1)))!=W/2) continue; balanced++;
      long[] N=new long[r+2]; for(int w=0;w<W;w++) if(((tt>>w)&1)==1) N[pc[w]]++;
      long s1=0,s2=0; boolean bad=false; for(int n=0;n<=r+1;n++){s1+=N[n];s2+=idN[n]; if(s1<s2) bad=true;}
      if(!surj(tt)) continue; surjCount++;
      if(bad){viol++; if(viol<20) System.out.println("VIOLATION r="+r+" rule="+Long.toBinaryString(tt)+" N="+Arrays.toString(N));}
    }
    System.out.println("r="+r+" balanced="+balanced+" surjective="+surjCount+" violations="+viol+" idN="+Arrays.toString(idN));
  }
}
