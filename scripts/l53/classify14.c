// Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
// N=14, mode ABC guards+N3. Classify N3 leaves: L = has R (|R|<=3) with sum = total (zero set >= 11);
// else P = has disjoint pair; else H = hard. Also count zero sets of size 10 etc.
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
static int ADD[64][64], NEG[64];
static uint64_t shift(uint64_t S, int x){ uint64_t T=0; while(S){int b=__builtin_ctzll(S); S&=S-1; T|=1ULL<<ADD[b][x];} return T;}
#define N 14
static inline int x1odd_or_x2odd(int x){ return (((x>>2)&3)|((x>>4)&3))&1; }
static inline int anyodd(int x){ return ((x&3)|((x>>2)&3)|((x>>4)&3))&1; }
static inline int x2odd(int x){ return ((x>>4)&3)&1; }
static int n3ok(const int *c){
  int mult[64]={0}; for(int i=0;i<N;i++) mult[c[i]]++;
  for(int x=1;x<64;x++){ if(anyodd(x) && mult[x]>mult[1]) return 0; if(x1odd_or_x2odd(x) && mult[x]>mult[4]) return 0; if(x2odd(x) && mult[x]>mult[16]) return 0; }
  return 1;
}
static int longz(const int *c){ int s=0; for(int i=0;i<N;i++) s=ADD[s][c[i]];
  if(s==0) return 1;
  for(int i=0;i<N;i++){ if(c[i]==s) return 1; for(int j=i+1;j<N;j++){ int a=ADD[c[i]][c[j]]; if(a==s) return 1; for(int k=j+1;k<N;k++) if(ADD[a][c[k]]==s) return 1; } }
  return 0; }
static int has_disjoint(const int *c){
  static __thread int sum[1<<N]; static __thread int zl[1<<N];
  int nz=0; sum[0]=0;
  for(int m=1;m<(1<<N);m++){ int b=__builtin_ctz(m); sum[m]=ADD[sum[m&(m-1)]][c[b]]; if(sum[m]==0) zl[nz++]=m; }
  for(int i=0;i<nz;i++) for(int j=i+1;j<nz;j++) if(!(zl[i]&zl[j])) return 1;
  return 0;
}
typedef struct { long long leaves,n3,L,P,H; } Stat;
static void dfs(int k, int *c, uint64_t R1, uint64_t R2, uint64_t R3, int has1, int has4, int has16, int no4, int no16, Stat *st, FILE *loc){
  if(k==N){ st->leaves++; if(!n3ok(c)) return; st->n3++;
    if(longz(c)) {st->L++; return;} if(has_disjoint(c)){ st->P++; if(loc){fprintf(loc,"P ");for(int i=0;i<N;i++) fprintf(loc,"%d ",c[i]); fprintf(loc,"\n");} return;} st->H++;
    if(loc){ fprintf(loc,"H "); for(int i=0;i<N;i++) fprintf(loc,"%d ",c[i]); fprintf(loc,"\n");} return; }
  int lo = k? c[k-1] : 1;
  for(int x=lo;x<64;x++){
    int h1=has1||x==1, h4=has4||x==4, h16=has16||x==16;
    int n4=no4 || (!has4 && x>4), n16=no16 || (!has16 && x>16);
    if(!h1 && anyodd(x)) continue; if(n4 && x1odd_or_x2odd(x)) continue; if(n16 && x2odd(x)) continue;
    if((R1|R2|R3)>>NEG[x]&1) continue;
    c[k]=x;
    dfs(k+1,c,R1|1ULL<<x, R2|shift(R1,x), R3|shift(R2,x), h1,h4,h16,n4,n16, st, loc);
  }
}
int main(int argc,char**argv){
  FILE *HF = argc>1? fopen(argv[1],"w"):NULL;
  for(int a=0;a<64;a++){ for(int b=0;b<64;b++){ int r=0; for(int i=0;i<3;i++){ int s=(((a>>(2*i))&3)+((b>>(2*i))&3))&3; r|=s<<(2*i);} ADD[a][b]=r; } }
  for(int a=0;a<64;a++) for(int b=0;b<64;b++) if(ADD[a][b]==0) NEG[a]=b;
  int pre[50000][3]; int np=0;
  for(int x0=1;x0<64;x0++) for(int x1=x0;x1<64;x1++) for(int x2=x1;x2<64;x2++){ pre[np][0]=x0; pre[np][1]=x1; pre[np][2]=x2; np++; }
  Stat tot; memset(&tot,0,sizeof tot);
  #pragma omp parallel for schedule(dynamic,1)
  for(int p=0;p<np;p++){
    Stat st; memset(&st,0,sizeof st); int c[24]; uint64_t R1=0,R2=0,R3=0; int has1=0,has4=0,has16=0,no4=0,no16=0; int ok=1;
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
    { tot.leaves+=st.leaves; tot.n3+=st.n3; tot.L+=st.L; tot.P+=st.P; tot.H+=st.H; }
  }
  if(HF) fclose(HF);
  printf("leaves=%lld N3=%lld long(>=11)=%lld pair(other)=%lld hard=%lld\n",tot.leaves,tot.n3,tot.L,tot.P,tot.H);
}
