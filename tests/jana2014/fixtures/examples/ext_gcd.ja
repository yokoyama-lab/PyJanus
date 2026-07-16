//////////////////////////////////////////////////////////////////////
// Reversible Extended Euclidean Algorithm
//
// Computes g = gcd(a,b) together with Bezout coefficients x0, y0 such
// that x0*A + y0*B = g (A, B the original inputs).  The classic
// iterative scheme; each step's quotient q is logged on `qlog`, which
// is exactly the information division destroys, so every step is
// reversible:
//   (a,b) -> (b, a mod b)     [a -= q*b; a <=> b]
//   (x0,x1) -> (x1, x0-q*x1)  [x0 -= q*x1; x0 <=> x1]
//   (y0,y1) -> (y1, y0-q*y1)
// Precondition: a >= 1, b >= 1.
//   forward: (a,b, x0=1,x1=0,y0=0,y1=1) -> (g, 0, bezout..., qlog)
//   uncall : restores the original state.
//////////////////////////////////////////////////////////////////////

procedure ext_gcd(int a, int b, int x0, int x1, int y0, int y1, stack qlog)
  from  empty(qlog)              // true only on entry
  loop  local int q = a / b
          a -= q * b             // a := a mod b
          a <=> b                // (a,b) := (b, a mod b)
          x0 -= q * x1
          x0 <=> x1
          y0 -= q * y1
          y0 <=> y1
          push(q,qlog)
        delocal int q = 0
  until b = 0

procedure main()
  int a
  int b
  int x0
  int x1
  int y0
  int y1
  stack qlog

  a += 240
  b += 46
  x0 += 1        // (x0,x1,y0,y1) = (1,0,0,1)
  y1 += 1

  call ext_gcd(a,b,x0,x1,y0,y1,qlog)
  // gcd(240,46) = 2;  x0*240 + y0*46 = 2  (x0=-9, y0=47)
