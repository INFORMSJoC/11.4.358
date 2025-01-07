      parameter (maxn=50)
      parameter (inf=99999999)

      common/ants/f,fb,l1,lb,glbound,tzub,tend,trail,rho,alpha,deltatau,
     +      size,level,as1,iprinx,vetmon,zub,delta,
     +      a,solbest,nants,basemod,fdom,symmetrical,
     +      dist,flow,cost,t0,t1,zopt
                               
      integer dist(maxn,maxn),flow(maxn,maxn),cost(maxn,maxn)

      real      f(maxn,maxn),fb(maxn,maxn)
c     integer asspar[maxn] 
      integer   size,level,as1,iprinx,vetmon(maxn),zub,delta(maxn,maxn)
      integer   a(maxn),solbest(maxn),nants,basemod,fdom,zopt
      real      l1,lb,glbound,tzub,tend,trail(maxn,maxn),rho,
     +          alpha,deltatau,t0,t1
      logical   symmetrical
