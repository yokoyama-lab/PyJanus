// bubble sort with optimal garbage
// Cormen, T. H., et al. (2009). Introduction to Algorithms third edition, The MIT Press. p.40

procedure bsort(int a[], int sz, stack gb)
  local int i=0
    from  i=0
    loop  local int j = sz - 1
            from  j = sz-1
            loop  if a[j] < a[j-1] then
                     local int t1 = a[j]  //  a[j-1] <=> a[j]
                       local int t2 = a[j-1]
                         a[j-1] ^= t1 ^ t2
                         a[j]   ^= t1 ^ t2
                       delocal int t2 = a[j]
                     delocal int t1 = a[j-1]
                     local int t = 1
                       push(t,gb)
                     delocal int t = 0
                  else
                     local int t = -1
                       push(t,gb)
                     delocal int t = 0
                  fi top(gb) = 1
                  j -= 1
            until j = i
          delocal int j = i
          i += 1
    until i=sz
  delocal int i=sz

procedure main()
  int a[6]     // input array
  int sz       // size of stk[]
  stack gb     // garbage stack
  int ord[6]   // permutation

  sz += 6
  a[0] += 50
  a[1] += 20
  a[2] += 40
  a[3] += 60
  a[4] += 10
  a[5] += 30

  call bsort(a,sz,gb)

  ord[0] += 0
  ord[1] += 1
  ord[2] += 2
  ord[3] += 3
  ord[4] += 4
  ord[5] += 5

  uncall bsort(ord,sz,gb)