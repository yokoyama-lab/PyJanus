//////////////////////////////////////////////////////////////////////
// Reversible AVL Tree -- Delete (with rotations)
// Nunez de Villavicencio, Emil, and Erik D. Demaine et al.,
//   "Energy-Efficient Algorithms" (arXiv:1605.08448), Section 5.3,
//   Theorem 6.12 (reversible Delete: O(lg n) time, +O(k) words of log
//   space over k deletes, 0 energy).
//
// Self-contained: includes reversible AVL insert (to build the tree)
// and delete.  Same array-based nodes as avl_insert.j
// (key/left/right/ht, index 0 = null).  Deletion is standard recursive
// AVL delete made reversible by logging every overwrite:
//   * alog -- overwritten child/root pointers AND the one key overwrite
//             in the two-children case (successor key copied up),
//   * hlog -- overwritten heights,
//   * rlog -- rotation codes (0 none / 1 LL / 2 RR / 3 LR / 4 RL),
//             here chosen from balance factors (no inserted key to test),
//   * dlog -- one bit per structural branch whose own condition it
//             mutates (which-child / one-vs-two-children), pushed at the
//             END of the branch so top(dlog) is a valid reversible exit
//             assertion.
// The successor's key is obtained reversibly by a compute-copy-uncompute
// descent (`minkey`), leaving no garbage.  Deleted nodes are unlinked but
// keep their slots (the paper's O(k) space growth); nothing is destroyed,
// so `uncall delete` re-inserts the key and restores the exact tree.
//////////////////////////////////////////////////////////////////////

// dev v2: reversible AVL delete (copy-successor-key approach)

procedure setchild(int arr[], int node, int val, stack alog)
  local int old = 0
    old ^= arr[node]
    arr[node] ^= old
    push(old,alog)
  delocal int old = 0
  arr[node] ^= val

procedure setroot(int root, int val, stack alog)
  local int old = 0
    old ^= root
    root ^= old
    push(old,alog)
  delocal int old = 0
  root ^= val

procedure hmax(int ht[], int ia, int ib, int out)
  if ht[ia] < ht[ib] then out ^= ht[ib] else out ^= ht[ia] fi ht[ia] < ht[ib]

procedure upht(int ht[], int left[], int right[], int node, stack hlog)
  local int m = 0
    call hmax(ht,left[node],right[node],m)
    local int old = 0
      old ^= ht[node]
      ht[node] ^= old
      push(old,hlog)
    delocal int old = 0
    ht[node] ^= m
    ht[node] += 1
  delocal int m = ht[node] - 1

procedure rot_right(int key[], int left[], int right[], int ht[],
                    int p, int ret, stack alog, stack hlog)
  local int l = left[p]
    call setchild(left,p,right[l],alog)
    call setchild(right,l,p,alog)
    call upht(ht,left,right,p,hlog)
    call upht(ht,left,right,l,hlog)
    ret ^= l
  delocal int l = ret

procedure rot_left(int key[], int left[], int right[], int ht[],
                   int p, int ret, stack alog, stack hlog)
  local int r = right[p]
    call setchild(right,p,left[r],alog)
    call setchild(left,r,p,alog)
    call upht(ht,left,right,p,hlog)
    call upht(ht,left,right,r,hlog)
    ret ^= r
  delocal int r = ret

// balance-factor based rebalance (works for both insert and delete)
procedure rebalance(int key[], int left[], int right[], int ht[],
                    int node, int ret, stack alog, stack hlog, stack rlog)
  call upht(ht,left,right,node,hlog)
  local int bf = ht[left[node]] - ht[right[node]]
    local int code = 0
      if bf > 1 then
        local int lbf = ht[left[left[node]]] - ht[right[left[node]]]
          if lbf < 0 then code += 3 else code += 1 fi lbf < 0
        delocal int lbf = ht[left[left[node]]] - ht[right[left[node]]]
      else
        if bf < -1 then
          local int rbf = ht[left[right[node]]] - ht[right[right[node]]]
            if rbf > 0 then code += 4 else code += 2 fi rbf > 0
          delocal int rbf = ht[left[right[node]]] - ht[right[right[node]]]
        fi bf < -1
      fi bf > 1
      push(code,rlog)
    delocal int code = 0
  delocal int bf = ht[left[node]] - ht[right[node]]
  if top(rlog) = 1 then
    call rot_right(key,left,right,ht,node,ret,alog,hlog)
  else
    if top(rlog) = 2 then
      call rot_left(key,left,right,ht,node,ret,alog,hlog)
    else
      if top(rlog) = 3 then
        local int sub = 0
          call rot_left(key,left,right,ht,left[node],sub,alog,hlog)
          call setchild(left,node,sub,alog)
        delocal int sub = left[node]
        call rot_right(key,left,right,ht,node,ret,alog,hlog)
      else
        if top(rlog) = 4 then
          local int sub = 0
            call rot_right(key,left,right,ht,right[node],sub,alog,hlog)
            call setchild(right,node,sub,alog)
          delocal int sub = right[node]
          call rot_left(key,left,right,ht,node,ret,alog,hlog)
        else
          ret ^= node
        fi top(rlog) = 4
      fi top(rlog) = 3
    fi top(rlog) = 2
  fi top(rlog) = 1

// ---- insert ----
procedure bins(int key[], int left[], int right[], int ht[],
               int node, int x, int nfree, int ret,
               stack alog, stack hlog, stack rlog)
  if node = 0 then
    ret ^= nfree
    key[nfree] ^= x
    ht[nfree] ^= 1
    nfree += 1
  else
    if x < key[node] then
      local int subret = 0
        call bins(key,left,right,ht,left[node],x,nfree,subret,alog,hlog,rlog)
        call setchild(left,node,subret,alog)
      delocal int subret = left[node]
    else
      local int subret = 0
        call bins(key,left,right,ht,right[node],x,nfree,subret,alog,hlog,rlog)
        call setchild(right,node,subret,alog)
      delocal int subret = right[node]
    fi x < key[node]
    call rebalance(key,left,right,ht,node,ret,alog,hlog,rlog)
  fi node = 0

procedure insert(int key[], int left[], int right[], int ht[],
                 int root, int x, int nfree,
                 stack alog, stack hlog, stack rlog)
  local int subret = 0
    call bins(key,left,right,ht,root,x,nfree,subret,alog,hlog,rlog)
    call setroot(root,subret,alog)
  delocal int subret = root

// ---- delete ----
// descend to the leftmost node of subtree; cur: node->0, ps top = leftmost
procedure descend_left(int left[], int cur, stack ps)
  from  empty(ps)
  loop  push(cur,ps)
        cur ^= left[top(ps)]
  until cur = 0

// sk := key of the minimum (leftmost) node of subtree `node`; no garbage
procedure minkey(int key[], int left[], int node, int sk)
  local int cur = node
    local stack ps = nil
      call descend_left(left,cur,ps)
      sk ^= key[top(ps)]
      uncall descend_left(left,cur,ps)
    delocal stack ps = nil
  delocal int cur = node

// remove the found node (key == x) itself; ret := replacement subtree root
procedure del_here(int key[], int left[], int right[], int ht[],
                   int node, int ret,
                   stack alog, stack hlog, stack rlog, stack dlog)
  // NB: the two-children branch calls rebalance(node), which may ROTATE node
  // and change left[node].  So the outer branch cannot use `fi left[node] = 0`
  // as its exit assertion; we log a decision bit and test top(dlog) instead.
  if left[node] = 0 then
    ret ^= right[node]                 // 0 or 1 (right) child
    local int b = 1
      push(b,dlog)
    delocal int b = 0
  else
    if right[node] = 0 then
      ret ^= left[node]                // 1 (left) child
      local int c = 0
        push(c,dlog)
      delocal int c = 0
    else
      local int sk = 0                 // two children: copy successor key up
        call minkey(key,left,right[node],sk)
        call setchild(key,node,sk,alog)          // key[node] := successor key
        local int subret = 0
          call del(key,left,right,ht,right[node],sk,subret,alog,hlog,rlog,dlog)
          call setchild(right,node,subret,alog)
        delocal int subret = right[node]
        call rebalance(key,left,right,ht,node,ret,alog,hlog,rlog)
      delocal int sk = key[node]
      local int c = 1
        push(c,dlog)
      delocal int c = 0
    fi top(dlog) = 0
    local int b = 0
      push(b,dlog)
    delocal int b = 0
  fi top(dlog) = 1

// delete key x from subtree `node` (assumed present); ret := new subtree root
procedure del(int key[], int left[], int right[], int ht[],
              int node, int x, int ret,
              stack alog, stack hlog, stack rlog, stack dlog)
  if x < key[node] then
    local int subret = 0
      call del(key,left,right,ht,left[node],x,subret,alog,hlog,rlog,dlog)
      call setchild(left,node,subret,alog)
    delocal int subret = left[node]
    call rebalance(key,left,right,ht,node,ret,alog,hlog,rlog)
    local int b = 0
      push(b,dlog)
    delocal int b = 0
  else
    if x > key[node] then
      local int subret = 0
        call del(key,left,right,ht,right[node],x,subret,alog,hlog,rlog,dlog)
        call setchild(right,node,subret,alog)
      delocal int subret = right[node]
      call rebalance(key,left,right,ht,node,ret,alog,hlog,rlog)
      local int b = 1
        push(b,dlog)
      delocal int b = 0
    else
      call del_here(key,left,right,ht,node,ret,alog,hlog,rlog,dlog)
      local int b = 2
        push(b,dlog)
      delocal int b = 0
    fi top(dlog) = 1
  fi top(dlog) = 0

procedure delete(int key[], int left[], int right[], int ht[],
                 int root, int x,
                 stack alog, stack hlog, stack rlog, stack dlog)
  local int subret = 0
    call del(key,left,right,ht,root,x,subret,alog,hlog,rlog,dlog)
    call setroot(root,subret,alog)
  delocal int subret = root
procedure main()
  int key[8]
  int left[8]
  int right[8]
  int ht[8]
  int root
  int nfree
  stack alog     // overwritten pointers & keys
  stack hlog     // overwritten heights
  stack rlog     // rotation codes
  stack dlog     // structural branch bits

  nfree += 1

  // build the balanced tree by inserting 1..7 (root = key 4)
  call insert(key,left,right,ht,root,1,nfree,alog,hlog,rlog)
  call insert(key,left,right,ht,root,2,nfree,alog,hlog,rlog)
  call insert(key,left,right,ht,root,3,nfree,alog,hlog,rlog)
  call insert(key,left,right,ht,root,4,nfree,alog,hlog,rlog)
  call insert(key,left,right,ht,root,5,nfree,alog,hlog,rlog)
  call insert(key,left,right,ht,root,6,nfree,alog,hlog,rlog)
  call insert(key,left,right,ht,root,7,nfree,alog,hlog,rlog)

  // delete the root (key 4): two children -> successor key 5 is copied up
  call delete(key,left,right,ht,root,4,alog,hlog,rlog,dlog)
  // resulting tree (root node still index 4, now holding key 5):
  //        5
  //       / \
  //      2   6
  //     / \   \
  //    1   3   7
  // node 5 (old key 5) is left detached as reversible garbage.
