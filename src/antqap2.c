/* ************************************************** */
/*  Approximate Nondeterministic Tree-search System:  */
/*  Quadratic Assignment Problems, 28/10/1996         */
/*  Version: Assignment bound at each node            */
/* ************************************************** */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <conio.h>
#include <string.h>
#include <math.h>

#define maxn 50
#define inf (long int) 99999999

                        /* prototipi delle funzioni */
void GLbound();
void antsearch();
void construct();
void input();
void printvet();
void printfvet();
void printlvet();
void printfmat();
void printmat();
void inizializza();
int  ordshelldecr();        /* ordinamento shell crescente   */
int  ordshellcres();        /*                   decrescente */
long int  zval();
int  montecarlo();
float lsap();
long int delta1();
long int delta2();
long int slocopt();
long int alocopt();
float rann();
int ranval();

                                                    /* variabili globali */
int    dist[maxn][maxn],    /* matrice delle distanze      */
       flow[maxn][maxn],    /* matrice dei pesi (o flussi) */
       cost[maxn][maxn];    /* matrice dei costi           */

float   f[maxn][maxn];  /* matrice f di uscita dalla GLbound */
float   fb[maxn][maxn]; /* matrice f di uscita dalla rule_b */
//int     asspar[maxn]; /* vettore della permutazione d'assegnamento parziale */
int     size;    /* intero che indica la dim. del problema */
int     level;   /* intero che indica la dim. dell'assegnamento parziale */
int     as1,iprinx,symmetrical=1;
long int vetmon[maxn];
long int zub;
int     a[maxn];      /* permutazione assegnamento per GL*/
int     solbest[maxn],nants,basemod,fdom;
float   l1,lb,glbound=0.,tzub,tend;
float   trail[maxn][maxn];
float   rho,alpha,deltatau;
clock_t t0,t1;

FILE    *fp,*fout,*fconf;


/* ********************************************************************* */
   void main()
/* ********************************************************************* */
{  int   maxiter,i,j,iter,irep,nrep;
   float u[maxn],v[maxn],l;

   if ((fconf=fopen("antqap.cfg","r"))==NULL)
   {  printf("error in opening config file\n");
      exit(1);
   }
   if ((fout=fopen("antqap.out","w"))==NULL)
   {  printf("error in opening output file\n");
      exit(1);
   }
   rann(-100);

   fscanf(fconf, "%5d %5d %5d %5d %5d %f %f",
	  &maxiter, &iprinx, &basemod, &nants, &nrep, &rho, &alpha);
   printf("\nmaxiter = %d iprinx = %d basemod = %d n.ants = %d nrep = %d rho = %2.2f alpha = %2.2f",
	     maxiter,iprinx,basemod,nants,nrep,rho,alpha);
   fprintf(fout,"\nmaxiter = %d iprinx = %d basemod = %d n.ants = %d nrep = %d rho = %2.2f alpha = %2.25.1f",
	     maxiter,iprinx,basemod,nants,nrep,rho,alpha);

   input();
   if(!symmetrical)
   {  nrep=0;
      printf("\n Asymmetric instance ...");
      goto end;
   }
                                 /* Gilmore-Lawler bound for the problem */
   GLbound();
   l=lsap(f,size,a,u,v);

   glbound=0;
   for(i=0;i<size;i++)
      glbound+=u[i]+v[i];

   if(iprinx>0)
   {  printf("\n u and v vectors");
      printf("\nu: ");fprintf(fout,"\nu: ");printfvet(u,size);
      printf("\nv: ");fprintf(fout,"\nv: ");printfvet(v,size);
        
      printf("\nGL lower bound = %10.2f verif. %10.2f",l,glbound);
      fprintf(fout,"\nGL lower bound = %10.2 verif. %10.2f",l,glbound);
      printf("\na: ");fprintf(fout,"\na: ");printvet(a,size);
   }

 for(irep=0;irep<nrep;irep++)
 { t0=clock();

   for(i=0;i<size;i++)
      for(j=0;j<size;j++)
         trail[i][j]=1;

   for(i=0;i<size;i++)   /* Initial assignment for ZUB intialization */
   {  a[i]=i;
      solbest[i]=a[i];
   }
   zub=zval(a,size);
   if(iprinx>0)
   {  printf ("\n Initial UB for assignment \n");
      printf("\na: ");fprintf(fout,"\na: ");printvet (a,size);
      printf ("\n ZUB : %d\n",zub);
      fprintf(fout,"\nInitial upper bound: %d",zub);
   }

   for (iter=0;iter<maxiter;iter++)
   {  if(iprinx>0)
      {  printf("\n========================= iterazione = %d",iter+1);
         fprintf(fout,"\n========================== iterazione = %d",iter+1);
      }
     
      antsearch(iter,u,v);               /* here the real thing goes on */
   } /* end for iter */

   t1=clock();
   tend = (1.0*(t1 - t0))/(1.0*CLK_TCK);
   printf ("\n assegnamento finale = ");
   fprintf (fout,"\n assegnamento finale = "); printvet (solbest,size);
   printf ("\n Probl. ZUB : %d",zub);
   fprintf (fout,"\n ZUB : %d",zub);
   printf (" GL-LB= %2.2f",glbound);
   fprintf (fout," GL-LB= %2.2f",glbound);
   printf (" T.cpu : %5.2f   T.tot.: %5.2f",tzub,tend);
   fprintf (fout," T.cpu : %5.2f   T.tot.: %5.2f ",tzub,tend);
 } /* for irep */


/*   printf("\npremi <return> per finire");   */
/*   fflush(stdin); getchar(); fflush(stdin); */

end:fclose(fout);
    printf("\nexiting");
    exit(1);

} /***** end of main *****/

/* ********************************************************************* */
		      void input()
/* ********************************************************************* */
/* funzione che carica le matrici del problema   */
{  int   i,j;

   inizializza();
   if ((fp=fopen("antqap.dat","r"))==NULL)
      {  printf("controllare nome file\n");
         exit(1);
      }

   fscanf(fp, " %d ", &size);
/*   printf("la dimensione e': < %d >\n", size); */

                          /* carico le tre matrici del problema */
   for (i=0; i<size; ++i)
       {  for (j=0; j<size; ++j)
            fscanf(fp, "%d", &dist[i][j]);
       }

   for (i=0; i<size; ++i)
       {  for (j=0; j<size; ++j)
             fscanf(fp, "%d", &flow[i][j]);
       }

   for (i=0; i<size; ++i)
       {  for (j=0; j<size; ++j)
             fscanf(fp, "%d", &cost[i][j]);
       }

   for (i=0; i<size; ++i)             /* controllo simmetria */
       {  for (j=0; j<size; ++j)
             if(dist[i][j]!=dist[j][i] ) symmetrical=0;
             if(flow[i][j]!=flow[j][i] ) symmetrical=0;
             if(cost[i][j]!=cost[j][i] ) symmetrical=0;
       }
/*
   printf("\nla matrice (d) delle distanze e' \n");
   printmat(dist,size);

   printf("\n\npremi <return> per continuare\n");
   fflush(stdin); getchar(); fflush(stdin);

   printf("\nla matrice (f) dei flussi e' \n");
   printmat(dist,size);

   printf("\n\npremi <return> per continuare\n");
   fflush(stdin); getchar(); fflush(stdin);

   printf("\nla matrice (c) dei costi e' \n");
   printmat(cost,size);

   printf("\n\npremi <return> per continuare\n");
   fflush(stdin); getchar(); fflush(stdin);
*/
} /* end  input */

/* ********************************************************************* */
   void GLbound()
/* ********************************************************************* */
/* implementazione del bound di Gilmor e Lawler  */
{ int      iw,jw,id,jd,y,k,i;
  long int w[maxn], d[maxn], ris;

/* passi 1. 2. 3. per il calcolo delle matrici e ed f */

for (iw=0; iw<size; ++iw)
   {  k=0;
      for (jw=0; jw<size; ++jw)
      {  if (iw!=jw)
         {  w[k]=dist[iw][jw];
            k++;
         }
      }

      for (id=0; id<size; ++id)
      {  y=0;
         for (jd=0; jd<size; ++jd)
         {  if (id!=jd)
            {  d[y]=flow[id][jd];
               y++;
            }
         }
         ordshelldecr(w,size-1);
         ordshellcres(d,size-1);

         ris=0;
         for (i=0; i<size-1; ++i)
            ris=ris+w[i]*d[i];
         f[iw][id]=(float) (cost[iw][id]+ris);

      } /* end for id */
   }  /* end for iw */
}     /* fine della rule a */

/* ********************************************************************* */
   void antsearch (int iter, float u[maxn], float v[maxn])
/* ********************************************************************* */
/* THE ant search */
{  int   i,j,iant,asspar[maxn];
   long int zcurr,kap;

   for(iant=0;iant<nants;iant++)
   {  fdom=0;
//      printf("\nStarting ant %d",iant);
      construct (asspar,u,v);          /* one ant solution */
//      printf(" end of ant %d fdom %d",iant, fdom);
      if(fdom==1) goto endant;

                         /* CHECK */
//      printf("\nAntsearch1, iant=%d, fdom=%d:",iant,fdom);printvet(asspar,size);

      zcurr=zval(asspar,size);

      if(iprinx>0)
      {  printf("\nasspar: ");fprintf(fout,"\nasspar: ");printvet(asspar,size);
         printf("\nZcurr= %ld, Starting local opt.\n",zcurr);
      }

      if(symmetrical)                            /* local optimization */
         zcurr = slocopt(asspar, zcurr);
      else
         zcurr = alocopt(asspar, zcurr);

      if(zcurr<glbound)
      {  printf("\nAntsearch: casino2! zub=%ld zlb=%f",zcurr,glbound);
         fflush(stdin); getchar(); fflush(stdin);         
      }
      if (zcurr<zub) /* riassegno se ho trovato un costo minore */
      {  zub=zcurr;
         t1=clock();
         tzub = 1.0*(t1 - t0)/(1.0*CLK_TCK);
         printf(" Time %5.2f",tzub);
         for(i=0;i<size;i++)
            solbest[i]=asspar[i];
      }
                                          /* trail updating */
      deltatau=(1.0*zcurr)/(1.0*size);
      for(i=0;i<size;i++)
         trail[i][asspar[i]]=rho*trail[i][asspar[i]]+deltatau;
       
      if((iter%basemod)==0 && iant==0)
      {  printf("\nIter %d costo = %d",iter,zcurr);
         fprintf(fout,"\nIter %d costo = %d",iter,zcurr);
         printf(" zub = %ld; tzub=%5.2f",zub,tzub);
         fprintf(fout," zub = %ld; tzub = %5.2f",zub,tzub);
      }

      if(iprinx>0)
      {  kap=zval(asspar,size);
         printf("\nCheck: zcurr= %ld",kap);
         printf("\nasspar: ");fprintf(fout,"\nasspar: ");printvet(asspar,size);
         printf("\npremi <return> per continuare");
         fflush(stdin); getchar(); fflush(stdin);
      }
endant:  i=0;  
   }   /* end for iant */
}

/* ********************************************************************* */
   void construct (int asspar[maxn],float u[maxn],float v[maxn])
/* ********************************************************************* */
/* constructs a solution */
{  int   tmp,ii,i,j,whonode[maxn];
   int   uflag[maxn],vflag[maxn],imont,elem;
   long int zcurr,b1,b2,kap,vetmax,vetmin;
   float nodebnd;

   zcurr=0;
   for(i=0;i<size;i++)
      uflag[i]=vflag[i]=asspar[i]=0;

   for (level=0; level<size-2; level++)
   { imont=-1;
     vetmax=-inf;
     vetmin=inf;
     for(j=0;j<size;j++)         /* calcola il bound per le alternative */
     {  if(vflag[j] == 0)
        {  asspar[level]=j;
           kap=zval(asspar,level);
           for(i=level+1;i<size;i++)
              kap+=u[i];
           for(i=0;i<size;i++)
              if(vflag[i]==0 && i!= j)
                 kap+= v[i];
           imont++;
           vetmon[imont]=(alpha)*kap+(1-alpha)*trail[level][j]; 
//           vetmon[imont]=kap;  
           whonode[imont]=j;
           if(vetmon[imont]>vetmax) vetmax=vetmon[imont];
           if(vetmon[imont]<vetmin) vetmin=vetmon[imont];
        }
     }    /* end for j eligible */

     if(iprinx>0)
     {  printf("\nvetmon:  ");fprintf(fout,"\nvetmon: ");printlvet(vetmon,imont);
        printf("\nvflag:   ");fprintf(fout,"\nvflag: ");printvet(vflag,size);
        printf("\nwhonode: ");fprintf(fout,"\nwhonode: ");printvet(whonode,size);
        printf("\nLevel= %d",level);
     }
          
     for(i=0;i<=imont;i++)
        vetmon[i]=100-(99.0/(vetmax-vetmin))*(vetmon[i]-vetmin);
     elem = montecarlo(vetmon, imont);
     if(iprinx>0)
     {  printf("\nvetmon:  ");fprintf(fout,"\nvetmon: ");printlvet(vetmon,imont);
        printf("\nElem= %d, imont=%d\n",elem,imont);
     }
     asspar[level]=whonode[elem];
     uflag[level]=1;
     vflag[whonode[elem]]=1;
/*   zcurr=zval(asspar,level+1);
     for (ii=0; ii<level; ii++)
        if (asspar[ii]==whonode[elem])
        {  printf("\ncasino! asspar=");printvet(asspar,level+1);
           printf("\nvetmon:  ");fprintf(fout,"\nvetmon: ");printlvet(vetmon,imont);
           printf("\nElem= %d, imont=%d\n",elem,imont);
           fflush(stdin); getchar(); fflush(stdin);
        }
*/
     nodebnd=(float) zval(asspar,level);
     for(i=level+1;i<size;i++)             /* guardo se il nodo e' dominato */
        nodebnd+=u[i];
     for(i=0;i<size;i++)
        if(vflag[i]==0 && i!= j)
           nodebnd+= v[i];
     if (nodebnd>=zub)
     {  fdom=1;
//        printf("\n Trovato nodo dominato: nodebnd %8.2f zub %ld",nodebnd,zub);
        goto endproc;
     }
     if (iprinx>0)
     {  printf("\nLevel = %d\n",level+1);
        fprintf(fout,"\nLevel = %d\n",level+1);
        printf("\nasspar: ");fprintf(fout,"\nasspar: ");printvet(asspar,level+1);
        printf("\nlower associato = %5.2f",nodebnd);
        fprintf(fout,"\nlower associato = %5.2f",nodebnd);
      } /* end if iprinx */
   }/* end for level */

        /* qui si assegnano nei due modi possibili le due risorse residue  */
   j=size-2;
   for (i=0; i<size; i++)
   {  if (vflag[i]==0)
      {  asspar[j]=i; /* eseguo l'assegnamento */
         j++;
      }
   }
   b1=zval(asspar,size); /* costo della prima permutazione */

   tmp=asspar[size-1];
   asspar[size-1]=asspar[size-2];
   asspar[size-2]=tmp;
                         /* CHECK */
//   for(i=1;i<size;i++)
//   {  for(j=0;j<i;j++)
//         if(asspar[i]==asspar[j])
//         {  printf("\n Construct: CASINO2! i=%d, j=%d",i,j);
//            printvet(asspar,size);
//            fflush(stdin); getchar(); fflush(stdin);
//         }
//   }
   b2=zval(asspar,size); /* costo della seconda permutazione */

   if(b1>b2)
      nodebnd=b2;
   else
   {  nodebnd=b1;
      tmp=asspar[size-1];
      asspar[size-1]=asspar[size-2];
      asspar[size-2]=tmp;
   }
endproc: i=0;
//   printf("\nConstruct1 fdom %d:",fdom);printvet(asspar,size);
}

/* ********************************************************************* */
   void printmat (int mat[maxn][maxn],int dim)
/* ********************************************************************* */
/* visualizza una matrice di interi a schermo */
{  int i,j;

   printf("\n");
   for (i=0; i<dim; i++)
   {  for (j=0; j<dim; j++)
         printf(" %3d", mat[i][j]);
      printf("\n");
   }
}

/* ********************************************************************* */
   void printfmat (float mat[maxn][maxn],int dim)
/* ********************************************************************* */
/* visualizza una matrice di float a schermo */
{ int i,j;

   printf("\n");
   for (i=0; i<dim; i++)
   {  for (j=0; j<dim; j++)
         printf(" %6.1f", mat[i][j]);
      printf("\n");
   }
}

/* ********************************************************************* */
		void printvet (int vet[maxn],int dim)
/* ********************************************************************* */
/* visualizza un vettore */
{  int i,k;
   k=0;
   printf("\n [");
   fprintf(fout,"\n [");
   for (i=0; i<dim; i++)
   {  if (k==20)
      {  k=0;
         printf("\n  ");
         fprintf(fout,"\n  ");

      }
      printf(" %2d", vet[i]);
      fprintf(fout," %2d", vet[i]);
      k++;
   }
   printf("  ]");
   fprintf(fout," ]");
}

/* ********************************************************************* */
		void printfvet (float vet[maxn],int dim)
/* ********************************************************************* */
/* visualizza un vettore reale */
{  int i,k;
   k=0;
   printf("\n [");
   fprintf(fout,"\n [");
   for (i=0; i<dim; i++)
   {  if (k==20)
      {  k=0;
         printf("\n  ");
         fprintf(fout,"\n  ");
      }
      printf(" %2.2f", vet[i]);
      fprintf(fout," %2.2f", vet[i]);
      k++;
   }
   printf("  ]\n");
   fprintf(fout," ]");
}

/* ********************************************************************* */
		void printlvet (long vet[maxn],int dim)
/* ********************************************************************* */
/* visualizza un vettore long */
{  int i,k;
   k=0;
   printf("\n [");
   fprintf(fout,"\n [");
   for (i=0; i<dim; i++)
   {  if (k==20)
      {  k=0;
         printf("\n  ");
         fprintf(fout,"\n  ");
      }
      printf(" %ld", vet[i]);
      fprintf(fout," %ld", vet[i]);
      k++;
   }
   printf("  ]\n");
   fprintf(fout," ]");
}


/* ********************************************************************* */
   int ordshellcres (long int *elementi,int quantita)
/* ********************************************************************* */
/* ordinamento di tipo shell in ordine crescente */
{  register long int i,j,gap,k;
   long int x, a[5];
   a[0]=9;
   a[1]=5;
   a[2]=3;
   a[3]=2;
   a[4]=1;

   for (k=0; k<5; k++)
   {  gap=a[k];
      for (i=gap; i<quantita; ++i)
      {  x=elementi[i];
         for (j=i-gap; x<elementi[j] && j>=0; j=j-gap)
         elementi[j+gap]=elementi[j];
         elementi[j+gap]=x;
      }
   }
   return *elementi;
}


/* ********************************************************************* */
   int ordshelldecr (long int *elementi,int quantita)
/* ********************************************************************* */
/* ordinamento di tipo shell in ordine decrescente */
{  register long int i,j,gap,k;
   long int x, a[5];
   a[0]=9;
   a[1]=5;
   a[2]=3;
   a[3]=2;
   a[4]=1;

   for (k=0; k<5; k++)
   {  gap=a[k];
      for (i=gap; i<quantita; ++i)
      {  x=elementi[i];
         for (j=i-gap; x>elementi[j] && j>=0; j=j-gap)
         elementi[j+gap]=elementi[j];
         elementi[j+gap]=x;
      }
   }
   return *elementi;
}

/* ********************************************************************* */
                       int tc(int *v,int lung)
/* ********************************************************************* */
/* costo totale (tc) per assegnamento a() */
{  int i,j,t,u;
   int ris;

   ris=0;
   for(i=0; i<lung; ++i)
      ris=ris+cost[i][v[i]-1];
   for(i=0; i<lung; ++i)
   {  t=v[i]-1;
      for(j=i; j<lung ; j++)
      {  u=v[j]-1;
         ris=ris+(dist[i][j]*flow[t][u]);
      }
   }
   return ris;
}

/* ********************************************************************* */
   float lsap(float d[maxn][maxn],int numtown,int vet[maxn],
                    float *ys, float *yt)
/* ********************************************************************* */
#define true (short int) 1
#define false (short int) 0

{  int riga[maxn],davanti[maxn];
   int index,j0,w,ind;
   float costocorr,ui,vj,lower,dminus[maxn],dplus[maxn],dd,vgl;
   short int label[maxn];
   register int i,j;
   int colonna[maxn];

/* ................................ inizializzazione variabili      */
   for(i=0;i<numtown;i++)
   {  riga[i]=-1;
      colonna[i]=-1;
      davanti[i]=-1;
      ys[i]=0;         /* costo minore per riga */
      yt[i]=0;
   }  /* end for 50 */

/* ................................. determina il valore minore per   */
/*                                   ogni riga e lo mette in ys       */

   for (i=0;i<numtown;i++)
   {  for (j=0;j<numtown;j++)  /* seleziona il costo minore nella riga i */
      {  /* e identifica colonna */
         costocorr = d[i][j];
         if (j==0 || costocorr<ui)
         {  ui=costocorr;    /* inizializza ui */
            j0=j;
         }
      }
      ys[i] = ui;        /* costo minore riga i */
      if(riga[j0]==-1)   /* se riga ha gia' un valore esci */
      {  riga[j0]=i;    /* riga[1]=0 => in riga 0 e colonna 1 c'e' il valore minore */
         colonna[i]=j0; /* clonna[0]=1 => in colonna 1, riga 1 c'e' il valore minore */
      }
   }

/* ...................................inizializzazione di yt in base ai */
/*                                    risultati precedenti              */
     for (j=0;j<numtown;j++)
       {  yt[j] = 0;
          if(riga[j]==-1)   /* non c'e' riga con costo minore in quella col */
          yt[j]=inf;     /* costo minore di colonna j */
       }

/*  sistemazione casi in cui non si e'                            */
/*  trovata una corrispondenza riga/colona                        */
/*  (tipicamente perche' in righe diverse i valori minori         */
/*   erano sulle stesse righe)                                    */

   for (i=0;i<numtown;i++) /* for 6 per tutte le righe */
   {  ui = ys[i];      /* costo minore della riga i */
      for (j=0;j<numtown;j++)   /* for 7 per tutte le colonne */
      {  vj = yt[j];   /* costo minore della colonna j */
         if(vj>0)
         {  costocorr = d[i][j] - ui;
            if (costocorr<vj)
            {  yt[j]  = costocorr;
               davanti[j] = i;
            }
         }
      }
   }

   for (j=0;j<numtown;j++)    /* for 8 */
   {  i = davanti[j];
      if (i!=-1 && colonna[i]==-1)
      {  colonna[i] = j;
         riga[j]  = i;
      }
   }

/* ..........................................................*/

   for (i=0;i<numtown;i++) /* for 9 */
   {  if(colonna[i]==-1)
      {  ui = ys[i];
         for (j=0;j<numtown;j++) /* for 10 */
         {  if(riga[j]==-1)
            {  costocorr = d[i][j];
               if((costocorr-ui-yt[j])<=0)
               {  colonna[i] = j;
                  riga[j]  = i;
                  break;
               }
            }
         }
      }
   }

/* ............................... costruzione dell'assegnamento ottimo */
for(j=0;j<numtown;j++)
   {  if(colonna[j]<0)
      {  for(i=0;i<numtown;i++)
         {  davanti[i] = j;
            label[i] = false;
            dplus[i] = inf;
            dminus[i] = d[j][i] - ys[j] - yt[i];
         }

         dplus[j] = 0;
         for (;;)
         {  dd=inf;
            for(i=0;i<numtown;i++) /* for 110 */
            {  if (!label[i] && dminus[i]<dd)
               {  dd=dminus[i];
                  index = i;
               }
            } /* end for 110 */

            if(riga[index]<0)
               break;

            label[index] = true;
            w=riga[index];
            dplus[w] = dd;

            for(i=0;i<numtown;i++)
            {  if (!label[i])
               {  vgl = dd + d[w][i] - ys[w] - yt[i];

                  if(dminus[i]>vgl)
                  {  dminus[i] = vgl;
                     davanti[i] = w;
                  }
               }
            }
         }

         for (;;)
         {  w=davanti[index];
            riga[index]=w;
            ind=colonna[w];
            colonna[w]=index;

            if(w==j)
               break;

            index = ind;
         }

/* ............................................................. */

         for(i=0;i<numtown;i++)
         {  if(dplus[i]!=inf)
               ys[i] += dd - dplus[i];

            if(dminus[i]<dd)
               yt[i] += dminus[i] - dd;
         }
      }
   }

/* ............................ calcolo del valore ottimo */
   lower=0;

   for(i=0;i<numtown;i++)
   {  j  = colonna[i];
      vet[i]=j;
      lower = lower + d[i][j];
   }
   return lower;
}

/* ********************************************************************* */
   long int zval(int *v,int lung)
/* ********************************************************************* */
/* funzione che calcola il costo totale (zval) per assegnamento a() */
{ int i,j,t,u;
  long int ris;

  ris=0;
  for(i=0; i<lung; ++i)
     ris=ris+cost[i][v[i]-1];
  for(i=0; i<lung; ++i)
  {  t=v[i];
     for(j=0; j<lung ; j++)
     {  u=v[j];
        ris=ris+(dist[i][j]*flow[t][u]);
     }
  }
  return ris;
}

/* ********************************************************************* */
   void inizializza(void)
/* ********************************************************************* */
/*  inizializza le matrici di lavoro    */
{ int i,j;
  size=0;
  for (i=0;i<maxn;i++)
  {  a[i]=0;
     for (j=0;j<maxn;j++)
     {  flow[i][j]=0;
        dist[i][j]=0;
        cost[i][j]=0;
        f[i][j]=0;
        fb[i][j]=0;
     }
  }
}

/* ********************************************************************* */
   int montecarlo (long vet[maxn],int size)
/* ********************************************************************* */
{ float sum,sum2,rnum;
  int i,j,k,sce;

  sum = 0.0;
  for (j=0; j<size; j++) sum = sum + vet[j];

  rnum = rann(1)*sum;

  sce = 0;
  sum2 = vet[sce];
  while (sum2 < rnum ) /* determinazione dell'elemento da prendere */
  {  sce++;
     sum2 = sum2 + vet[sce];
  }
  return sce;
}

/* ********************************************************************* */
   long int alocopt(int *permut, long int zcurr)
/* ********************************************************************* */
/* local search for asymmetric instances */
{  int i,j,k,u,v;
   int temp_u,temp_v,temp;
   int flag_primo_delta;
   int flag_cambiamento;
   long int delta_minimo,delta[maxn][maxn],df;

   u=0;
   v=0;
   flag_primo_delta=1;
   flag_cambiamento=0;
   do
   {  delta_minimo=99999999;
      for(i=0;i<size;++i)
      {  for(j=0;j<size;++j)
         {  if ((flag_primo_delta!=1)&&(i!=u)&&(i!=v)&&(j!=u)&&(j!=v))
            {  df=delta2(permut,delta,u,v,i,j);
               delta[i][j]+=df; 
            }
            else
            {  df=delta1(permut,delta,i,j);
               delta[i][j]=df;
            }

            if (delta[i][j]<delta_minimo)
            {  temp_u=i;
               temp_v=j;
               delta_minimo=delta[i][j];
            };
         };
      };
      u=temp_u;
      v=temp_v;
      flag_primo_delta=0;
      if (delta_minimo<0){
         zcurr=zcurr+delta_minimo;
         temp=permut[u];
         permut[u]=permut[v];
         permut[v]=temp;
      }
      else
         flag_cambiamento=1;
   }while (flag_cambiamento!=1);
   if(iprinx>0)
   {  printf("\nPermut: ");fprintf(fout,"\npermut: ");printvet(permut,size);
      printf("\nLocopt. Zcurr: %ld",zcurr);
   }
   return(zcurr);
};

/* ********************************************************************* */
   long int slocopt(int *permut, long int zcurr)
/* ********************************************************************* */
/* local search for symmetric instances */
{  int i,j,k,u,v;
   int temp_u,temp_v,temp;
   int flag_primo_delta;
   int flag_cambiamento;
   long int delta_minimo,delta[maxn][maxn],df;

   u=0;
   v=0;
   flag_primo_delta=1;
   flag_cambiamento=0;
   do
   {  delta_minimo=99999999;
      for(i=0;i<size-1;++i)
      {  for(j=i+1;j<size;++j)
         {  if ((flag_primo_delta!=1)&&(i!=u)&&(i!=v)&&(j!=u)&&(j!=v))
            {  df=delta2(permut,delta,u,v,i,j);
               delta[i][j]+=2*df;
            }
            else
            {  df=delta1(permut,delta,i,j);
               delta[i][j]=2*df;
            }

            if (delta[i][j]<delta_minimo)
            {  temp_u=i;
               temp_v=j;
               delta_minimo=delta[i][j];
            };
         };
      };
      u=temp_u;
      v=temp_v;
      flag_primo_delta=0;
      if (delta_minimo<0)
      {  zcurr=zcurr+delta_minimo;
         temp=permut[u];
         permut[u]=permut[v];
         permut[v]=temp;
      }
      else
         flag_cambiamento=1;
   }while (flag_cambiamento!=1);

   if(iprinx>0)
   {  printf("\nPermut: ");fprintf(fout,"\npermut: ");printvet(permut,size);
      printf("\nLocopt. Zcurr: %ld",zcurr);
   }
   if(zcurr<glbound)
   {  printf("\nPermut: ");fprintf(fout,"\npermut: ");printvet(permut,size);
      printf("\nLocopt. Zcurr: %ld",zcurr);
   }
   return(zcurr);
};

/* ********************************************************************* */
   long int delta1(int permut[maxn],long int delta[maxn][maxn], int i,int j)
/* ********************************************************************* */
{  int k;
   long int res;

   delta[i][j]=0;
   for(k=0;k<size;++k)
      if((k!=i)&&(k!= j))
         delta[i][j]+=(dist[i][k]-dist[j][k])*
                      (flow[permut[j]][permut[k]]-flow[permut[i]][permut[k]]);
/*   delta[i][j]=res=2*delta[i][j]; */
   res=delta[i][j];
   return(res);
};

/* ********************************************************************* */
   long int delta2(int permut[maxn],long int delta[maxn][maxn],
               int i,int j,int u,int v)
/* ********************************************************************* */
{       long int a1,a2,a3,a4,b1,b2,b3,b4,res;

        a1=dist[i][u];
        a2=dist[i][v];
        a3=dist[j][v];
        a4=dist[j][u];

        b1=flow[permut[j]][permut[u]];
        b2=flow[permut[j]][permut[v]];
        b3=flow[permut[i]][permut[v]];
        b4=flow[permut[i]][permut[u]];

/*        delta[u][v]+=2*(a1-a2+a3-a4)*(b1-b2+b3-b4); */
        res = (a1-a2+a3-a4)*(b1-b2+b3-b4);
        return(res);
};

/* ********************************************************************* */
   float rann(int a)
/* ********************************************************************* */
/* a < 0 to initialize */
{  static long seed;
   long int ia,ic,im;
   float rnd;
   int i;

   ia=7141;
   ic=54733;
   im=259200;
   if(a<0)
   {  seed=0;
      for(i=1;i<500;i++)
         rnd=rann(1);
   }
   seed=seed*ia+ic;
   seed=seed - seed/im * im;
   rnd=(seed+0.0)/im;
   return rnd;
}

/* ********************************************************************* */
   int ranval(int a, int b)
/* ********************************************************************* */
{  int rnv;
   rnv=a+rann(1)*(b-a+1);
   return rnv;
}


//   for i := 1 to n-1 do 
//      for j := i+1 to n do
//         if (i<>u) and (i<>v) and (j<>u) and (j<>v) then
//            delta_short_computation(u,v, i,j)
//         else delta_full_computation(i,j);


void delta_full_computation(long int i,j);
/* computes the difference of solution values if units u and v are permuted */
long int k, sum;
{  sum=0;
   for {k=0;k<n;k++}
      if ((k!=i) && (k!=j))
         sum := sum + a[k][i]*(b[p[k]][p[j]]-b[p[k]][p[i]]) +
                      a[k][j]*(b[p[k]][p[i]]-b[p[k]][p[j]]) + 
                      a[i][k]*(b[p[j]][p[k]]-b[p[i]][p[k]]) +
                      a[j][k]*(b[p[i]][p[k]]-b[p[j]][p[k]]);
   sum := sum + a[i][i]*(b[p[j]][p[j]]-b[p[i]][p[i]]) +
                a[i][j]*(b[p[j]][p[i]]-b[p[i]][p[j]]) +
                a[j][i]*(b[p[i]][p[j]]-b[p[j]][p[i]]) +
                a[j][j]*(b[p[i]][p[i]]-b[p[j]][p[j]]);
   delta[i][j]=sum;
}

void delta_short_computation(long int r,s,i,j);
/* idem but needs the value of delta[u,v] before the exchange of i and j  */
{  delta[i][j]= delta[i][j] + 
                (a[r][i]-a[r][j]+a[s][j]-a[s][i])*
                 (b[p[s]][p[i]]-b[p[s]][p[j]]+b[p[r]][p[j]]-b[p[r]][p[i]]) +
                (a[i][r]-a[j][r]+a[j][s]-a[i][s])*
                 (b[p[i]][p[s]]-b[p[j]][p[s]]+b[p[j]][p[r]]-b[p[i]][p[r]])
}
