c * ************************************************** */
c *  Approximate Nondeterministic Tree-search System:  */
c *  Quadratic Assignment Problem, 30/10/1996          */
c * ************************************************** */

c ********************************************************************* */
      program main
c ********************************************************************* */
      include 'antqap.inc'
      include 'lsap.inc'

      integer maxiter,i,j,iter,irep,nrep,sumzub,minzub
      real u(maxn),v(maxn),avgzub,avgtzub,mintzub,sumtzub

      open(unit=5,file='antqap.cfg')
      open(unit=4,file='antqap.out')
      sumzub =0
      minzub =inf
      mintzub=inf
      sumtzub=0.0
      sumttot=0.0
   
      read(5,*)     maxiter
      read(5,*)     iprinx
      read(5,*)     basemod
      read(5,*)     nants
      read(5,*)     nrep
      read(5,*)     rho
      read(5,*)     alpha
      write(*,1000) maxiter,iprinx,basemod,nants,nrep,rho,alpha
      write(4,1000) maxiter,iprinx,basemod,nants,nrep,rho,alpha
 1000 format('maxiter',i5,' iprinx',i5,' basemod',i5,' n.ants',i5,
     +       ' nrep',i5,' rho',f4.2,' alpha',f4.2)

      call input
      if(.not.symmetrical) then
         nrep=0
         write(*,*)' Asymmetric instance ...'
         write(4,*)' Asymmetric instance ...'
         goto 9999
      endif

c     ---------------------------- Gilmore-Lawler bound for the problem 
c     size: dimensione della matrice, asimmetrica
c     cass : matrice dei costi dell'assegnamento

      call GL_bound
      do i=1,size
         do j=1,size
            cass((i-1)*size+j) = f(i,j)
         enddo   
      enddo
      call lsap(size,lbgl)
      zlb=lbgl
   
      glbound=0
      do i=1,size
         u(i)=ys(i)
         v(i)=yt(i)
         glbound=glbound+u(i)+v(i)
      enddo
   
      if(iprinx.gt.0) then
         write(*,*)'u and v vectors'
         write(4,*)'u and v vectors'
         write(*,*)'u: ',(u(i),i=1,size)
         write(4,*)'u: ',(u(i),i=1,size)
         write(*,*)'v: ',(v(i),i=1,size)
         write(4,*)'v: ',(v(i),i=1,size)
           
         write(*,*) 'GL lower bound =',zlb,' verif.',glbound
         write(4,*) 'GL lower bound =',zlb,' verif.',glbound
      endif
   
      do 100 irep=1,nrep
         call clock(t0)
         zub=inf
   
         do i=1,size
            do j=1,size
               trail(i,j)=1
            enddo
         enddo
   
c        ----------------------- Initial assignment for ZUB intialization
         do i=1,size
            a(i)=i
            solbest(i)=a(i)
         enddo
         zub=izval(a,size)

         if(iprinx.gt.0) then
            write(*,*)' Initial UB for assignment'
            write(*,*)'a: ',(a(i),i=1,size)
            write(4,*)'a: ',(a(i),i=1,size)
            write(*,*)' initial upper bound:',zub
            write(4,*)' initial upper bound:',zub
         endif
      
         do iter=1,maxiter
            if(iprinx.gt.0) then
               write(*,*) '========================= iterazione = ',iter
               write(4,*) '========================= iterazione = ',iter
            endif
c           ----------------------------  here the real thing goes on */
            call antsearch(iter,u,v)
            if(zub-glbound.lt.0.00001) goto 200
         enddo
      
  200    call clock(t1)
         tend = t1-t0
c         write(*,*)'assegnamento finale=',(solbest(i),i=1,size)
c         write(4,*)'assegnamento finale=',(solbest(i),i=1,size)
         write(*,*)' Final ZUB:',zub
         write(4,*)' Final ZUB:',zub
         write(*,*)' GL-LB=',glbound
         write(4,*)' GL-LB=',glbound
         write(*,*)' T.cpu:',tzub,' T.tot.:',tend
         write(4,*)' T.cpu:',tzub,' T.tot.:',tend
         if(zub.lt.minzub)minzub=zub
         if(tzub.lt.mintzub) mintzub=tzub
         sumzub=sumzub+zub
         sumtzub=sumtzub+tzub
         sumttot=sumttot+tend
  100 continue
      avgzub=sumzub/nrep
      avgtzub=sumtzub/nrep
      avgttot=sumttot/nrep
      write(*,2000)minzub,mintzub,avgzub,avgtzub,avgttot
      write(4,2000)minzub,mintzub,avgzub,avgtzub,avgttot
 2000 format('minzub',i10,' mintzub',f10.2,' avgzub',f12.2,
     +       ' avgtzub',f12.2,' avgttot',f12.2)

 9999 close(4)
      write(*,*) 'exiting'
   
      stop
      end

c ********************************************************************* */
      subroutine input()
c ********************************************************************* */
c carica le matrici del problema   */
      include 'antqap.inc'
      integer   i,j

      call inizializza
      open(unit=3,file='antqap.dat')

      read(3,*)size
      write(*,*)'dimensione =',size

c     -------------------------  carico le tre matrici del problema */
      do i=1,size
         read(3,*) (dist(i,j),j=1,size)
      enddo
      read(3,*)

      do i=1,size
         read(3,*) (flow(i,j),j=1,size)
      enddo
      read(3,*,err=999)

      do i=1,size
         read(3,*,err=999) (cost(i,j),j=1,size)
      enddo

c     ------------------------------- controllo simmetria */
 999  symmetrical=.true.
      do i=1,size
          do j=1,size
              if(dist(i,j).ne.dist(j,i)) symmetrical=.false.
              if(flow(i,j).ne.flow(j,i)) symmetrical=.false.
              if(cost(i,j).ne.cost(j,i)) symmetrical=.false.
              if(.not.symmetrical) goto 100
          enddo
      enddo
  100 continue

      if(iprinx.gt.1) then
         write(*,*) 'matrice (d) delle distanze'
         do i=1,size
            write(*,*) (dist(i,j),j=1,size)
         enddo
         write(*,*)'premi .lt.return.gt. per continuare'
         read(*,*)
   
         write(*,*) 'matrice (f) dei flussi'
         do i=1,size
            write(*,*) (flow(i,j),j=1,size)
         enddo
         write(*,*)'premi .lt.return.gt. per continuare'
         read(*,*)
   
         write(*,*) 'matrice (c) dei costi'
         do i=1,size
            write(*,*) (cost(i,j),j=1,size)
         enddo
         write(*,*)'premi .lt.return.gt. per continuare'
         read(*,*)
      endif

      return
      end

c ********************************************************************* */
      subroutine GL_bound()
c ********************************************************************* */
c preprocessing del bound di Gilmor e Lawler 
      include 'antqap.inc'
      integer iw,jw,id,jd,y,k,i,temp(maxn)
      integer*2 ind(maxn)
      integer w(maxn), d(maxn), ris

      do 100 iw=1,size
         k=1
         do jw=1,size
            if (iw.ne.jw) then
               w(k)=dist(iw,jw)
               k=k+1
            endif
         enddo
      
         do 200 id=1,size
            y=1
            do jd=1,size
               if (id.ne.jd) then
                  d(y)=flow(id,jd)
                  y=y+1
               endif
            enddo
            call sorti4(w,ind,size-1,1)
            do i=1,size-1
               temp(i)=w(ind(i))
            enddo
            do i=1,size-1
               w(i)=temp(i)
            enddo
            call sorti4(d,ind,size-1,0)
            do i=1,size-1
               temp(i)=d(ind(i))
            enddo
            do i=1,size-1
               d(i)=temp(i)
            enddo

            ris=0
            do i=1,size-1
               ris=ris+w(i)*d(i)
            enddo
            f(iw,id)=1.0*(cost(iw,id)+ris)

  200    continue
  100 continue

      return
      end

c ********************************************************************* */
      subroutine construct(asspar,u,v)
c ********************************************************************* */
c constructs a solution */
      include 'antqap.inc'

      integer asspar(maxn)
      integer tmp,i,j,whonode(maxn),uflag(maxn),vflag(maxn)
      integer zcurr,b1,b2,kap,vetmax,vetmin,imont,elem
      real    u(maxn),v(maxn),nodebnd

      zcurr=0
      do i=1,size
         uflag(i)=0
         vflag(i)=0
         asspar(i)=0
      enddo

      do 100 level=1,size-2
         imont=0
         vetmax=-inf
         vetmin=inf
c        --------------------------- calcola il bound per le alternative */
         do 200 j=1,size
            if(vflag(j).eq.0) then
               asspar(level)=j
               kap=izval(asspar,level)
               do i=level+1,size
                  kap=kap+u(i)
               enddo
               do i=1,size
                  if(vflag(i).eq.0 .and. i.ne.j) kap= kap+v(i)
               enddo
               imont=imont+1
c               vetmon(imont)=(alpha)*kap+(1-alpha)*trail(level,j) 
               vetmon(imont)=kap  
               whonode(imont)=j
               if(vetmon(imont).gt.vetmax) vetmax=vetmon(imont)
               if(vetmon(imont).lt.vetmin) vetmin=vetmon(imont)
            endif
  200    continue

        if(iprinx.ge.0) then
           write(*,*)'vetmon:  ',(vetmon(i), i=1,imont)
           write(*,*)'vflag:   ',(vflag(i),  i=1,size)
           write(*,*)'whonode: ',(whonode(i),i=1,size)
           write(*,*)'Level=',level
           write(4,*)'vetmon:  ',(vetmon(i), i=1,imont)
           write(4,*)'vflag:   ',(vflag(i),  i=1,size)
           write(4,*)'whonode: ',(whonode(i),i=1,size)
           write(4,*)'Level=',level
        endif
             
        do i=1,imont
           vetmon(i)=100-(99.0/(1+vetmax-vetmin))*(vetmon(i)-vetmin)
        enddo
        elem = montecarlo(vetmon,imont)
        if(iprinx.gt.0) then
           write(*,*)'vetmon:  ',(vetmon(i),i=1,imont)
           write(*,*)'Elem=',elem,' imont',imont
           write(4,*)'vetmon:  ',(vetmon(i),i=1,imont)
           write(4,*)'Elem=',elem,' imont',imont
           write(4,*)
        endif

        asspar(level)=whonode(elem)
        uflag(level)=1
        vflag(whonode(elem))=1
c        zcurr=izval(asspar,level+1)
c
        nodebnd=izval(asspar,level)
c       -----------------------          guardo se il nodo e' dominato */
        do i=level+1,size
           nodebnd=nodebnd+u(i)
        enddo
        do i=1,size
           if((vflag(i).eq.0).and.(i.ne.j)) nodebnd=nodebnd+v(i)
        enddo
        if (nodebnd.ge.zub) then
           fdom=1
c           write(*,*)  Trovato nodo dominato: '
           goto 9999
        endif

        if (iprinx.gt.0) then
           write(*,*)'Level =',level+1
           write(4,*)'Level =',level+1
           write(*,*)'asspar: ',(asspar(i),i=1,level+1)
           write(4,*)'asspar: ',(asspar(i),i=1,level+1)
           write(*,*)'lower bound associato = ',nodebnd
        endif
  100 continue

c     -------- qui si assegnano le due risorse residue 
      j=size-1
      do i=1,size
         if (vflag(i).eq.0) then
c           --------------------------------     eseguo l'assegnamento */
            asspar(j)=i
            j=j+1
         endif
      enddo
c     ------------------------------- costo della prima permutazione */
      b1=izval(asspar,size) 
   
      tmp=asspar(size)
      asspar(size)=asspar(size-1)
      asspar(size-1)=tmp

c     ----------------------------- costo della seconda permutazione */
      b2=izval(asspar,size) 
   
      if(b1.gt.b2) then
         nodebnd=b2
      else
         nodebnd=b1
         tmp=asspar(size)
         asspar(size)=asspar(size-1)
         asspar(size-1)=tmp
      endif

 9999 continue

      return
      end

c ********************************************************************* */
      subroutine antsearch (iter,u,v)
c ********************************************************************* */
c THE ant search 
      include 'antqap.inc'
      integer iter,i,iant,asspar(maxn),zcurr,kap
      real    u(maxn), v(maxn)

      do 100 iant=1,nants
         fdom=0
c        write(*,*) Starting ant',iant
c        ------------------------------------------- one ant solution 
         call construct(asspar,u,v)
c        write(' end of ant',iant,'fdom ', fdom)
         if(fdom.eq.1) goto 100

         zcurr=izval(asspar,size)
         if(iprinx.ge.1) then
            write(*,1100) zcurr,(asspar(i),i=1,size)
            write(4,1100) zcurr,(asspar(i),i=1,size)
 1100       format('ST: Zcurr:',i10,' asspar:',(15i3))
         endif

c     -----------------------------------------  local optimization */
         call improve_qap_solution(asspar,zcurr)
         if(iprinx.ge.1) then
            write(*,1101) zcurr,(asspar(i),i=1,size)
            write(4,1101) zcurr,(asspar(i),i=1,size)
 1101       format('EN: Zcurr:',i10,' asspar:',(15i3))
         endif
      
         if(zcurr.lt.glbound) then
            write(*,*) 'Antsearch: casino2! zub=',zcurr,' zlb=',glbound
            read(*,*)
         endif
         if(zcurr-glbound.lt.0.0001) then
            write(*,*) 'Antsearch: Ottimo! zub=',zcurr,' zlb=',glbound
            goto 9999
         endif

c        ----------------------- riassegno se ho trovato un costo minore */
         if (zcurr.lt.zub) then
            zub=zcurr
            call clock(t1)
            tzub = t1-t0
            write(*,*)' Time ',tzub,' zub',zub
            write(4,*)' Time ',tzub,' zub',zub
            do i=1,size
               solbest(i)=asspar(i)
            enddo
         endif
c        ------------------------------------------------ trail updating */
         deltatau=(1.0*zcurr)/(1.0*size)
         do i=1,size
            trail(i,asspar(i))=rho*trail(i,asspar(i))+deltatau
         enddo
       
         if(mod(iter,basemod).eq.0 .and. iant.eq.0) then
            write(*,*)'Iter',iter,' costo',zcurr
            write(4,*)'Iter',iter,' costo',zcurr
            write(*,*)' zub =',zub,' tzub=',tzub
            write(4,*)' zub =',zub,' tzub=',tzub
         endif

         if(iprinx.gt.0) then
            kap=izval(asspar,size)
            write(*,*) 'Check: zcurr=',kap
            write(*,*) 'asspar:',(asspar(i),i=1,size)
            write(*,*) 'premi return per continuare'
            read(*,*)
         endif
  100 continue
 9999 continue
      return
      end

c ********************************************************************* */
      integer function izval(vett,lung)
c ********************************************************************* */
c funzione che calcola il costo totale (izval) per assegnamento a()
      include 'antqap.inc'
      integer vett(*),lung
      integer i,j,t,u,ris

      ris=0
      do i=1,lung
         ris=ris+cost(i,vett(i))
      enddo
      do i=1,lung
         t=vett(i)
         do j=1,lung
            u=vett(j)
            ris=ris+(dist(i,j)*flow(t,u))
         enddo
      enddo
      izval=ris

      return
      end

c ********************************************************************* */
      subroutine inizializza
c ********************************************************************* */
c  inizializza le matrici di lavoro    */
      include 'antqap.inc'
      integer i,j
      size=0
      do i=1,maxn
         a(i)=0
         do j=1,maxn
            flow(i,j)=0
            dist(i,j)=0
            cost(i,j)=0
            f(i,j)=0
            fb(i,j)=0
         enddo
      enddo
      return
      end

c ********************************************************************* */
      integer function montecarlo(vet,nn)
c ********************************************************************* */
      include 'antqap.inc'
      real    sum,sum2,rnum
      integer nn,j,sce,vet(*)

      sum = 0.0
      do j=1,nn
         sum = sum + vet(j)
      enddo
      rnum = random(1.)
      rnum = rnum*sum
      sce  = 1
      sum2 = vet(sce)
c     --------------------- determinazione dell'elemento da prendere */
      while (sum2.lt.rnum) do
         sce  = sce+1
         sum2 = sum2 + vet(sce)
      endwhile
      montecarlo=sce

      return
      end

c ********************************************************************* */
      subroutine delta_full_computation(i,j,p)
c ********************************************************************* */
c computes the difference of solution values if units u and v are permuted */
      include 'antqap.inc'
      integer k,sum,i,j,p(*)

      sum=0
      do k=1,size
         if ((k.ne.i) .and. (k.ne.j)) then
            sum= sum + flow(k,i)*(dist(p(k),p(j))-dist(p(k),p(i))) +
     +                 flow(k,j)*(dist(p(k),p(i))-dist(p(k),p(j))) + 
     +                 flow(i,k)*(dist(p(j),p(k))-dist(p(i),p(k))) +
     +                 flow(j,k)*(dist(p(i),p(k))-dist(p(j),p(k)))
         endif
      enddo
      sum=sum + flow(i,i)*(dist(p(j),p(j))-dist(p(i),p(i))) +
     +          flow(i,j)*(dist(p(j),p(i))-dist(p(i),p(j))) +
     +          flow(j,i)*(dist(p(i),p(j))-dist(p(j),p(i))) +
     +          flow(j,j)*(dist(p(i),p(i))-dist(p(j),p(j)))
      delta(i,j)=sum
      return
      end

c ********************************************************************* */
      subroutine delta_short_computation(r,s,i,j,p)
c ********************************************************************* */
c idem but needs the value of delta(u,v) before the exchange of i and j  */
      include 'antqap.inc'
      integer r,s,i,j,p(*)

      delta(i,j)=delta(i,j) + 
     +             (flow(r,i)-flow(r,j)+flow(s,j)-flow(s,i))*
     +                (dist(p(s),p(i))-dist(p(s),p(j))+
     +                 dist(p(r),p(j))-dist(p(r),p(i)))+
     +             (flow(i,r)-flow(j,r)+flow(j,s)-flow(i,s))*
     +                (dist(p(i),p(s))-dist(p(j),p(s))+
     +                 dist(p(j),p(r))-dist(p(i),p(r)))
      return
      end

c ********************************************************************* */
      subroutine init_delta(asspar,zcurr)
c ********************************************************************* */
      include 'antqap.inc'
      integer i,j,asspar(*),zcurr

      zcurr = 0
      do i=1,size
         do j=1,size
            zcurr = zcurr + flow(i,j) * dist(asspar(i),asspar(j))
            if (i.lt.j) then
               call delta_full_computation(i,j,asspar)
            endif
         enddo
      enddo

      return
      end

c ********************************************************************* */
      subroutine find_best_move(u,v)
c ********************************************************************* */
      include 'antqap.inc'
      integer i,j,u,v,delta_min

      n=size
      delta_min = inf
      u = inf
      do i = 1,n-1
         do j = i+1,n
            if ((delta(i,j).lt.delta_min)) then 
               u = i
               v = j
               delta_min = delta(i,j)
            endif
         enddo
      enddo
      return
      end

c ********************************************************************* */
      subroutine perform_one_move(asspar,zcurr)
c ********************************************************************* */
      include 'antqap.inc'
      integer i, j, u, v,temp,asspar(*),zcurr

      n=size
      call  find_best_move(u,v)
      if (u.ne.inf) then
         zcurr = zcurr + delta(u,v)
         temp=asspar(u)
         asspar(u)=asspar(v)
         asspar(v)=temp
      end if
      if (zcurr.lt.zub) then
         zub=zcurr
         call clock(t1)
         tzub = t1-t0
         write(*,*)' Time ',tzub,' zub',zub
         write(4,*)' Time ',tzub,' zub',zub
         do i=1,size
            solbest(i)=asspar(i)
         enddo
      endif
      do i = 1,n-1
         do j = i+1,n 
            if ((i.ne.u).and.(i.ne.v).and.(j.ne.u).and.(j.ne.v)) then
                call delta_short_computation(u,v,i,j,asspar)
            else
                call delta_full_computation(i,j,asspar)
            endif
         enddo
      enddo
      return
      end

c ********************************************************************* */
      subroutine improve_qap_solution(asspar,zcurr)
c ********************************************************************* */
      include 'antqap.inc'
      integer zold,asspar(*),zcurr

      call init_delta(asspar,zcurr)
  10  zold=zcurr
         call perform_one_move(asspar,zcurr)
      if(zcurr.lt.zold) goto 10

      return
      end

