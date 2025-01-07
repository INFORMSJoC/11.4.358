c ----------------------------------------------------------------------
      subroutine lsap(n,z)
c ----------------------------------------------------------------------
      implicit integer (a-z)
      include 'lsap.inc'

      dimension zeile(nverb2),dminus(nverb2),dplus(nverb2),
     +      vor(nverb2)
      logical label(nverb2)

c
c      write(*,*) '  inizia lsap: n= ',n
c
      sup = 1000000000
      do 50 i=1,n
       zeile(i)  = 0
       spalte(i) = 0
       vor(i)    = 0
       ys(i)     = 0
       yt(i)     = 0
   50 continue
      ik = 0
      do 2 i=1,n
       do 3 j=1,n
          ik = ik + 1
          cc = cass(ik)
          if(j.eq.1) go to 4
          if( (cc-ui) .ge. 0) go to 3
    4       ui = cc
          j0 = j
    3    continue
       ys(i) = ui
       if(zeile(j0).ne.0) go to 2
       zeile(j0) = i
       spalte(i) = j0
    2 continue
      do 5 j=1,n
       yt(j) = 0
       if(zeile(j).eq.0) yt(j) = sup
    5 continue
      ik = 0
      do 6 i=1,n
       ui = ys(i)
       do 7 j=1,n
          ik = ik + 1
          vj = yt(j)
          if(vj.le.0) go to 7
          cc = cass(ik) - ui
          if(cc.ge.vj) go to 7
          yt(j)  = cc
          vor(j) = i
    7    continue
    6 continue
      do 8 j=1,n
       i = vor(j)
       if(i.eq.0) go to 8
       if(spalte(i).ne.0) go to 8
       spalte(i) = j
       zeile(j)  = i
    8 continue
      do 9 i=1,n
       if(spalte(i).ne.0) go to 9
       ui = ys(i)
       ik = (i-1)*n
       do 10 j=1,n
          ik = ik + 1
          if(zeile(j).ne.0) go to 10
          cc = cass(ik)
          if(cc-ui-yt(j) .gt. 0) go to 10
          spalte(i) = j
          zeile(j)  = i
          go to 9
   10    continue
    9 continue
c
c     Construction of the optimal assignment
c
c      write(*,*) ' entra nel do 1000 '
c
      do 1000 u=1,n
       if(spalte(u).gt.0) go to 1000
c
       us = (u-1)*n
       do 100 i=1,n
          vor(i)    = u
          label(i)  = .false.
          dplus(i)  = sup
          usi       = us + i
          dminus(i) = cass(usi) - ys(u) - yt(i)
  100    continue
       dplus(u) = 0
  105    d = sup
       do 110 i=1,n
          if(label(i)) go to 110
          if(dminus(i).ge.d) go to 110
          d     = dminus(i)
          index = i
  110    continue
       if(zeile(index).le.0) go to 400
       label(index) = .true.
       w = zeile(index)
       ws = (w-1)*n
       dplus(w) = d
       do 130 i=1,n
          if(label(i)) go to 130
          wsi = ws + i
          vgl = d + cass(wsi) - ys(w) - yt(i)
          if(dminus(i).le.vgl) go to 130
          dminus(i) = vgl
          vor(i)    = w
  130    continue
       go to 105
c
  400    w            = vor(index)
       zeile(index) = w
       ind          = spalte(w)
       spalte(w)    = index
       if(w.eq.u) go to 500
       index = ind
       go to 400
c
  500    do 510 i=1,n
          if(dplus(i).eq.sup) go to 505
          ys(i) = ys(i) + d - dplus(i)
  505       if(dminus(i).ge.d) go to 510
          yt(i) = yt(i) + dminus(i) - d
  510    continue
 1000 continue
c
c     Computation of the optimal value
c
      z = 0
      do 2000 i=1,n
       is = (i-1)*n
       j  = spalte(i)
       isj = is + j
       z = z + cass(isj)
 2000 continue
      return
      end

