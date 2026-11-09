const fs=require('fs'),path=require('path'),dir=__dirname;
const graphs=JSON.parse(fs.readFileSync(path.join(dir,'search-input.json')));
function pc(x){x=x-((x>>>1)&0x55555555);x=(x&0x33333333)+((x>>>2)&0x33333333);return (((x+(x>>>4))&0x0f0f0f0f)*0x01010101)>>>24;}
function base(g){let a=Array(g.n).fill(0);for(let [u,v] of g.edges){a[u]|=1<<v;a[v]|=1<<u;}let entries=[];
 for(let S=0;S<(1<<g.n);S++){let k=pc(S),e=0,q=0,z=0,c=0,todo=S;for(let i=0;i<g.n;i++)if(S>>i&1){e+=pc(a[i]&S);q+=pc(a[i]&~S);}else z+=!(a[i]&S);e/=2;
 if(g.tree)c=k-e;else while(todo){c++;let front=todo&-todo;while(front){todo&=~front;let adj=0;while(front){let i=31-Math.clz32(front&-front);front&=front-1;adj|=a[i];}front=adj&todo;}}
 let key=k;for(let x of [e,c,q,z])key=key*64+x;entries.push(key);
 }return {a,entries};}
function sig(g,r,bas){let {a,entries}=bas||base(g);let res=new Float64Array(entries.length);for(let S=0;S<res.length;S++){let b=S>>r&1,d=+(!b&&!!(a[r]&S));res[S]=((entries[S]-(!b&&!d))*64+b)*64+d;}return res.sort();}
function hash(s){let h1=2166136261,h2=123456789;for(let v of s){let lo=v>>>0,hi=Math.floor(v/4294967296);h1=Math.imul(h1^lo,16777619);h1=Math.imul(h1^hi,16777619);h2=Math.imul(h2^hi,2246822519);h2=Math.imul(h2^lo,3266489917);}return (h1>>>0)+','+(h2>>>0);}
let start=Date.now(),seen=new Map(),equalities=[],roots=0,done=0;let cap=150000;
for(let id=0;id<graphs.length;id++){if(Date.now()-start>cap)break;let g=graphs[id],bas=base(g);for(let r of g.roots){let s=sig(g,r,bas),h=g.n+','+g.edges.length+','+hash(s),bucket=seen.get(h)||[];for(let [j,u] of bucket){let t=sig(graphs[j],u);if(s.every((v,i)=>v===t[i]))equalities.push([id,r,j,u]);}bucket.push([id,r]);seen.set(h,bucket);roots++;}done++;}
fs.writeFileSync(path.join(dir,'rooted-equalities.json'),JSON.stringify(equalities));let result={graphs:done,roots,exact_equalities:equalities.length,seconds:(Date.now()-start)/1000,complete:done===graphs.length,wall_cap_seconds:150};fs.writeFileSync(path.join(dir,'rooted-diagnostics.json'),JSON.stringify(result,null,2));console.log(result);
module.exports={base,sig};
