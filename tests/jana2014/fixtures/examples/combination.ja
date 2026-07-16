// iterative factorial: linear time
procedure factI(int n, int res)
  res ^= 1
  local int i = 0
    from  i = 0
    loop  local int tmp = res
            res ^= tmp ^ tmp * (n - i)
          delocal int tmp = res / (n - i)
          i += 1
    until i = n
  delocal int i = n

// iterative implementation of permutation
procedure permI(int n, int r, int res)
  res ^= 1
  local int i = 0
    from  i = 0
    loop  local int tmp = res
            res ^= tmp ^ tmp * (n - i)
          delocal int tmp = res / (n - i)
          i += 1
    until i = r
  delocal int i = r

// using subfunctions: exponential time
procedure combS(int n, int r, int res)
  if r >= 0 then  // if r is negative, res=0
  local int p = 0
    call permI(n, r, p)
    local int f = 0
      call factI(r, f)
      res += p / f
      f -= p / res
      // uncall fact(r, f)
    delocal int f = 0
    uncall permI(n, r, p)
  delocal int p = 0
  fi r >= 0

//////////////////////////////////////////////////////////////////////
// iterative combination
procedure combI(int n, int r, int res)
  if r >= 0 then  // if r is negative, res=0
    res ^= 1
    local int i = 0
      from  i = 0
      loop  local int tmp = res
              res ^= tmp ^ tmp * (n - i)
            delocal int tmp = res / (n - i)
            i += 1
      until i = r
    delocal int i = r

    local int i = r
      from  i = r
      loop  local int tmp = res / i
              res ^= tmp ^ tmp * i
            delocal int tmp = res
            i -= 1
      until i = 0
    delocal int i = 0
  fi r >= 0

procedure main()
  int n
  int r
  int res

  n += 5
  r += 2
  call combI(n,r,res)