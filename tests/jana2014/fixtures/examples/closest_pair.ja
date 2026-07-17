//////////////////////////////////////////////////////////////////////
// Reversible Closest Pair of Points (brute force, squared distances)
//
// Points (x[i], y[i]) with integer coordinates.  Scans all pairs
// i < j, folding the minimum SQUARED distance into a temporary with an
// overwrite log + decision bits; the result is copied out and the fold
// uncalled to erase the logs (Bennett compute-copy-uncompute).
// Everything is integer arithmetic, so the result is exact.  0 energy.
// Precondition: n >= 2.
//   forward: res = min over i<j of (x[i]-x[j])^2 + (y[i]-y[j])^2
//////////////////////////////////////////////////////////////////////

procedure cp_sub(int x[], int y[], int n, int best, int big,
                 stack lg, stack bl)
  local int i = 0
    from  i = 0
    loop  local int j = i + 1
            from  j = i + 1
            loop  local int d = (x[i]-x[j])*(x[i]-x[j]) + (y[i]-y[j])*(y[i]-y[j])
                    if d < best then
                      push(best,lg)      // log previous minimum, best -> 0
                      best += d
                      local int b = 1
                        push(b,bl)
                      delocal int b = 0
                    else
                      local int b = 0
                        push(b,bl)
                      delocal int b = 0
                    fi top(bl) = 1
                  delocal int d = (x[i]-x[j])*(x[i]-x[j]) + (y[i]-y[j])*(y[i]-y[j])
                  j += 1
            until j = n
          delocal int j = n
          i += 1
    until i = n - 1
  delocal int i = n - 1

procedure closest_pair(int x[], int y[], int n, int big, int res)
  local int best = big
    local stack lg = nil
      local stack bl = nil
        call cp_sub(x,y,n,best,big,lg,bl)
        res ^= best                        // copy the answer out
        uncall cp_sub(x,y,n,best,big,lg,bl)
      delocal stack bl = nil
    delocal stack lg = nil
  delocal int best = big

procedure main()
  int x[5]
  int y[5]
  int n
  int big
  int res

  n += 5
  big += 1000000

  x[0] += 2   y[0] += 3
  x[1] += 12  y[1] += 30
  x[2] += 40  y[2] += 50
  x[3] += 5   y[3] += 1
  x[4] += 12  y[4] += 10

  call closest_pair(x,y,n,big,res)
  // closest pair: (2,3)-(5,1), squared distance 9+4 = 13
