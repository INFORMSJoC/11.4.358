      SUBROUTINE SORTI4(A,V,N,IORD)
C     IORD = 0, SORT IN INCREASING ORDER.
C          = 1, SORT IN DECREASING ORDER.
      DIMENSION A(N),V(N)
      INTEGER*4 A
      INTEGER*2 IU(16),IL(16),V
      INTEGER*4 T,TT
      II=1
      JJ=N
      DO 200 I=1,N
  200 V(I)=I
      IF(N.LE.1) RETURN
      M=1
      I=II
      J=JJ
    5 IF(I.GE.J) GO TO 70
   10 K=I
      IJ=(J+I)/2
      IV=V(IJ)
      T=A(IV)
      IF(A(V(I)).LE.T) GO TO 20
      V(IJ)=V(I)
      V(I)=IV
      IV=V(IJ)
      T=A(IV)
   20 L=J
      IF(A(V(J)).GE.T) GO TO 40
      V(IJ)=V(J)
      V(J)=IV
      IV=V(IJ)
      T=A(IV)
      IF(A(V(I)).LE.T) GO TO 40
      V(IJ)=V(I)
      V(I)=IV
      IV=V(IJ)
      T=A(IV)
      GO TO 40
   30 V(L)=V(K)
      V(K)=IVT
   40 L=L-1
      IF(A(V(L)).GT.T) GO TO 40
      IVT=V(L)
      TT=A(IVT)
   50 K=K+1
      IF(A(V(K)).LT.T) GO TO 50
      IF(K.LE.L) GO TO 30
      IF(L-I.LE.J-K) GO TO 60
      IL(M)=I
      IU(M)=L
      I=K
      M=M+1
      GO TO 80
   60 IL(M)=K
      IU(M)=J
      J=L
      M=M+1
      GO TO 80
   70 M=M-1
      IF(M.EQ.0) GO TO 210
      I=IL(M)
      J=IU(M)
   80 IF(J-I.GE.II) GO TO 10
      IF(I.EQ.II) GO TO 5
      I=I-1
   90 I=I+1
      IF(I.EQ.J) GO TO 70
      IV=V(I+1)
      T=A(IV)
      IF(A(V(I)).LE.T) GO TO 90
      K=I
  100 V(K+1)=V(K)
      K=K-1
      IF(T.LT.A(V(K))) GO TO 100
      V(K+1)=IV
      GO TO 90
C  CHECK FOR DECREASING ORDER.
  210 IF(IORD.EQ.0) RETURN
      N1=N+1
      NH=N/2
      DO 230 I=1,NH
      II=N1-I
      IV=V(I)
      V(I)=V(II)
      V(II)=IV
  230 CONTINUE
      RETURN
      END
