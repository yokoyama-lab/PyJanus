//////////////////////////////////////////////////////////////////////
// Reversible Topological Sort (DFS post-order)
//
// DAG as adjacency matrix adj[u*V+v].  A reversible DFS records each
// vertex's post-order position; the reverse of the post-order is a
// topological order.  Every branch whose condition its own body
// mutates (visited tests) logs one decision bit on `blog`, pushed at
// the END of the branch so top(blog) is a valid reversible exit
// assertion.  0 energy.
//   outputs: order[k] = k-th vertex in POST-order (read right-to-left
//   for the topological order), visited[], blog.
//////////////////////////////////////////////////////////////////////

procedure dfs_post(int adj[], int v_n, int u, int visited[], int order[],
                   int cnt, stack blog)
  visited[u] += 1
  local int v = 0
    from  v = 0
    loop  if adj[u*v_n+v] = 1 && visited[v] = 0 then
            call dfs_post(adj,v_n,v,visited,order,cnt,blog)
            local int b = 1
              push(b,blog)
            delocal int b = 0
          else
            local int b = 0
              push(b,blog)
            delocal int b = 0
          fi top(blog) = 1
          v += 1
    until v = v_n
  delocal int v = v_n
  order[cnt] ^= u          // post-order position (written once)
  cnt += 1

procedure toposort(int adj[], int v_n, int visited[], int order[], stack blog)
  local int cnt = 0
    local int u = 0
      from  u = 0
      loop  if visited[u] = 0 then
              call dfs_post(adj,v_n,u,visited,order,cnt,blog)
              local int b = 1
                push(b,blog)
              delocal int b = 0
            else
              local int b = 0
                push(b,blog)
              delocal int b = 0
            fi top(blog) = 1
            u += 1
      until u = v_n
    delocal int u = v_n
  delocal int cnt = v_n

procedure main()
  int adj[25]     // 5x5 DAG
  int v_n
  int visited[5]
  int order[5]    // post-order; reversed = topological order
  stack blog

  v_n += 5

  // DAG edges: 0->1 0->2 1->3 2->3 3->4
  adj[0*5+1] += 1
  adj[0*5+2] += 1
  adj[1*5+3] += 1
  adj[2*5+3] += 1
  adj[3*5+4] += 1

  call toposort(adj,v_n,visited,order,blog)
  // post-order = {4, 3, 1, 2, 0} -> topological order 0,2,1,3,4
