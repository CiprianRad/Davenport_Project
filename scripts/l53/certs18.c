// Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
// For each 18-term rep: find zero set B and a 5-set I_1 certificate (A1+A2+A3 = D1+D2) inside S = complement of B.
// I_2 certificate: +B, +Ai, -(Ai|B), -Dj, +(Dj|B).  Output masks and coefficients.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
#define N 18
static int ADD[64][64];
int main(int argc,char**argv){
  for(int a=0;a<64;a++) for(int b=0;b<64;b++){ int r=0; for(int i=0;i<3;i++){ int s=(((a>>(2*i))&3)+((b>>(2*i))&3))&3; r|=s<<(2*i);} ADD[a][b]=r; }
  FILE *f=fopen(argv[1],"r"); int (*seqs)[N]=malloc(sizeof(int)*N*1000); int n=0;
  while(fscanf(f,"%d",&seqs[n][0])==1){ for(int i=1;i<N;i++) if(fscanf(f,"%d",&seqs[n][i])!=1) return 1; n++; }
  char **out=calloc(n,sizeof(char*)); int none=0;
  #pragma omp parallel for schedule(dynamic,1) reduction(+:none)
  for(int s=0;s<n;s++){
    int *c=seqs[s]; int M=1<<N; int *sum=malloc(sizeof(int)*M); unsigned char *isz=malloc(M); int *Z=malloc(sizeof(int)*M);
    int nz=0; sum[0]=0; isz[0]=0;
    for(int m=1;m<M;m++){ int b=__builtin_ctz(m); sum[m]=ADD[sum[m&(m-1)]][c[b]]; isz[m]=sum[m]==0; if(isz[m]) Z[nz++]=m; }
    int found=0; char buf[512]; int *ZS=malloc(sizeof(int)*nz);
    for(int bi=0;bi<nz&&!found;bi++){ int B=Z[bi]; int S=(M-1)&~B;
      int ns=0; for(int i=0;i<nz;i++) if(!(Z[i]&B)) ZS[ns++]=Z[i];
      for(int i=0;i<ns&&!found;i++) for(int j=i+1;j<ns&&!found;j++){
        int D=ZS[i],E=ZS[j]; int U=D^E, I=D&E, W=D|E;
        for(int a=0;a<ns&&!found;a++){ int A=ZS[a]; if(A&~W) continue;
          for(int b=a+1;b<ns&&!found;b++){ int Bb=ZS[b]; if(Bb&~W) continue; if(A&Bb&U) continue; if(I&~(A|Bb)) continue;
            int C=(U&~A&~Bb)|(I&(A^Bb)); if(C==0||!isz[C]) continue;
            sprintf(buf,"%d 1 %d 1 %d 1 %d 1 %d -1 %d -1 %d -1 %d -1 %d -1 %d 1 %d 1",B,A,Bb,C,A|B,Bb|B,C|B,D,E,D|B,E|B); found=1; (void)S; }
        }
      }
    }
    if(!found){ none++; sprintf(buf,"NONE"); }
    out[s]=strdup(buf); free(sum); free(isz); free(Z); free(ZS);
  }
  FILE *o=fopen(argv[2],"w");
  for(int s=0;s<n;s++){ for(int i=0;i<N;i++) fprintf(o,"%d ",seqs[s][i]); fprintf(o,"| %s\n",out[s]); }
  fclose(o); printf("reps=%d none=%d\n",n,none);
}
