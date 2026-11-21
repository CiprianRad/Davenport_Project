// Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
// General N. Enumerate sorted SZF N-lists with guards (A),(B),(C) [e1/e2/e3 present or parity condition],
// count nodes per depth, leaves, N3 leaves; classify N3 leaves; write hard N3 leaves.
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
static int ADD[64][64], NEG[64];
static uint64_t shift(uint64_t S, int x){ uint64_t T=0; while(S){int b=__builtin_ctzll(S); S&=S-1; T|=1ULL<<ADD[b][x];} return T;}
static int N;
static inline int x1odd_or_x2odd(int x){ return (((x>>2)&3)|((x>>4)&3))&1; }
static inline int anyodd(int x){ return ((x&3)|((x>>2)&3)|((x>>4)&3))&1; }
static inline int x2odd(int x){ return ((x>>4)&3)&1; }
static int n3ok(const int *c, int mode){
  int mult[64]={0}; for(int i=0;i<N;i++) mult[c[i]]++;
  for(int x=1;x<64;x++){
    if(anyodd(x) && mult[x]>mult[1]) return 0;
    if(mode>=2 && x1odd_or_x2odd(x) && mult[x]>mult[4]) return 0;
    if(mode>=3 && x2odd(x) && mult[x]>mult[16]) return 0; }
  return 1;
}
// classification for N=14: has 2 disjoint zero sets. N=18: 3 disjoint zero sets, or zero set size>=15.
static int classify(const int *c){
  int M=1<<N; static __thread int *sum=NULL; static __thread int *zl=NULL; if(!sum){sum=malloc(sizeof(int)*(1<<18)); zl=malloc(sizeof(int)*(1<<18));}
  int nz=0; sum[0]=0;
  for(int m=1;m<M;m++){ int b=__builtin_ctz(m); sum[m]=ADD[sum[m&(m-1)]][c[b]]; if(sum[m]==0) zl[nz++]=m; }
  if(N==14){ for(int i=0;i<nz;i++) for(int j=i+1;j<nz;j++) if(!(zl[i]&zl[j])) return 1; return 0; }
  for(int i=0;i<nz;i++) if(__builtin_popcount(zl[i])>=15) return 2;
  for(int i=0;i<nz;i++) for(int j=i+1;j<nz;j++) if(!(zl[i]&zl[j])) { int u=zl[i]|zl[j]; for(int k=j+1;k<nz;k++) if(!(zl[k]&u)) return 1; }
  return 0;
}
typedef struct { long long nodes[24]; long long leaves, n3[4], cls[3]; } Stat;
static int MODE=3;
static FILE *HF;
static void dfs(int k, int *c, uint64_t R1, uint64_t R2, uint64_t R3, int has1, int has4, int has16, int no4, int no16, Stat *st, FILE *loc){
  st->nodes[k]++;
  if(k==N){ st->leaves++;
    for(int md=1;md<=3;md++) st->n3[md]+=n3ok(c,md);
    if(n3ok(c,MODE)){ int r=classify(c); st->cls[r]++; if(r==0&&loc){ for(int i=0;i<N;i++) fprintf(loc,"%d ",c[i]); fprintf(loc,"\n");} }
    return; }
  int lo = k? c[k-1] : 1;
  for(int x=lo;x<64;x++){
    // guard A: if 1 not present, all elements must have all coords even
    int h1=has1||x==1, h4=has4||x==4, h16=has16||x==16;
    int n4=no4 || (!has4 && x>4), n16=no16 || (!has16 && x>16);
    if(!h1 && anyodd(x)) continue;           // no e1 => all even (sorted: 1 is the least odd-type code)
    if(n4 && x1odd_or_x2odd(x)) continue;    // skipped past 4 => all x1,x2 even afterwards
    if(n16 && x2odd(x)) continue;            // skipped past 16 => all x2 even afterwards
    if((R1|R2|R3)>>NEG[x]&1) continue;
    if(x==0) continue;
    c[k]=x;
    dfs(k+1,c,R1|1ULL<<x, R2|shift(R1,x), R3|shift(R2,x), h1,h4,h16,n4,n16, st, loc);
  }
}
int main(int argc,char**argv){
  N=atoi(argv[1]); MODE=atoi(argv[2]); HF = argc>3? fopen(argv[3],"w"):NULL;
  for(int a=0;a<64;a++){ for(int b=0;b<64;b++){ int r=0; for(int i=0;i<3;i++){ int s=(((a>>(2*i))&3)+((b>>(2*i))&3))&3; r|=s<<(2*i);} ADD[a][b]=r; } }
  for(int a=0;a<64;a++) for(int b=0;b<64;b++) if(ADD[a][b]==0) NEG[a]=b;
  // split on first three codes
  int pre[50000][3]; int np=0;
  for(int x0=1;x0<64;x0++) for(int x1=x0;x1<64;x1++) for(int x2=x1;x2<64;x2++){ pre[np][0]=x0; pre[np][1]=x1; pre[np][2]=x2; np++; }
  Stat tot; memset(&tot,0,sizeof tot);
  #pragma omp parallel for schedule(dynamic,1)
  for(int p=0;p<np;p++){
    Stat st; memset(&st,0,sizeof st);
    int c[24]; 
    // replay prefix through same rules by a mini-dfs restricted to the prefix
    uint64_t R1=0,R2=0,R3=0; int has1=0,has4=0,has16=0,no4=0,no16=0; int ok=1;
    for(int k=0;k<3;k++){ int x=pre[p][k];
      int h1=has1||x==1, h4=has4||x==4, h16=has16||x==16; int n4=no4||(!has4&&x>4), n16=no16||(!has16&&x>16);
      if(!h1&&anyodd(x)){ok=0;break;} if(n4&&x1odd_or_x2odd(x)){ok=0;break;} if(n16&&x2odd(x)){ok=0;break;}
      if((R1|R2|R3)>>NEG[x]&1){ok=0;break;}
      c[k]=x; uint64_t n3=R3|shift(R2,x), n2=R2|shift(R1,x); R1|=1ULL<<x; R2=n2; R3=n3; has1=h1;has4=h4;has16=h16;no4=n4;no16=n16; }
    if(!ok) continue;
    char *mem=NULL; size_t msz=0; FILE *loc = HF? open_memstream(&mem,&msz):NULL;
    dfs(3,c,R1,R2,R3,has1,has4,has16,no4,no16,&st,loc);
    if(loc){ fclose(loc);
      #pragma omp critical
      fwrite(mem,1,msz,HF);
      free(mem);}
    #pragma omp critical
    { for(int i=0;i<24;i++) tot.nodes[i]+=st.nodes[i]; tot.leaves+=st.leaves; for(int i=0;i<4;i++) tot.n3[i]+=st.n3[i]; for(int i=0;i<3;i++) tot.cls[i]+=st.cls[i]; }
  }
  if(HF) fclose(HF);
  long long tn=0; for(int i=3;i<=N;i++){ tn+=tot.nodes[i]; printf("depth %d nodes %lld\n",i,tot.nodes[i]); }
  printf("N=%d total nodes(>=3)=%lld leaves=%lld N3[A]=%lld N3[AB]=%lld N3[ABC]=%lld | mode %d classes: hard=%lld witness=%lld long=%lld\n",N,tn,tot.leaves,tot.n3[1],tot.n3[2],tot.n3[3],MODE,tot.cls[0],tot.cls[1],tot.cls[2]);
}
