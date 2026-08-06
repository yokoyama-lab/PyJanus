"""A textbook AVL tree in the array-of-nodes shape the examples use.

Node 0 is the null pointer; real nodes are handed out in insertion order from
`nfree`, which is what makes the arrays comparable with the Janus programs'.
Deletion copies the in-order successor's key up and unlinks the successor,
leaving the vacated slot's key array entry as it was.
"""


class Avl:
  def __init__(self, size):
    self.key = [0] * size
    self.left = [0] * size
    self.right = [0] * size
    self.ht = [0] * size
    self.root = 0
    self.nfree = 1

  def height(self, node):
    return self.ht[node] if node else 0

  def _update(self, node):
    self.ht[node] = 1 + max(self.height(self.left[node]), self.height(self.right[node]))

  def _balance(self, node):
    return self.height(self.left[node]) - self.height(self.right[node])

  def _rotate_right(self, node):
    pivot = self.left[node]
    self.left[node], self.right[pivot] = self.right[pivot], node
    self._update(node)
    self._update(pivot)
    return pivot

  def _rotate_left(self, node):
    pivot = self.right[node]
    self.right[node], self.left[pivot] = self.left[pivot], node
    self._update(node)
    self._update(pivot)
    return pivot

  def _rebalance(self, node):
    self._update(node)
    bias = self._balance(node)
    if bias > 1:
      if self._balance(self.left[node]) < 0:
        self.left[node] = self._rotate_left(self.left[node])
      return self._rotate_right(node)
    if bias < -1:
      if self._balance(self.right[node]) > 0:
        self.right[node] = self._rotate_right(self.right[node])
      return self._rotate_left(node)
    return node

  def insert(self, target):
    self.root = self._insert(self.root, target)

  def _insert(self, node, target):
    if node == 0:
      node, self.nfree = self.nfree, self.nfree + 1
      self.key[node] = target
      self.ht[node] = 1
      return node
    if target < self.key[node]:
      self.left[node] = self._insert(self.left[node], target)
    else:
      self.right[node] = self._insert(self.right[node], target)
    return self._rebalance(node)

  def delete(self, target):
    self.root = self._delete(self.root, target)

  def _delete(self, node, target):
    if node == 0:
      return 0
    if target < self.key[node]:
      self.left[node] = self._delete(self.left[node], target)
    elif target > self.key[node]:
      self.right[node] = self._delete(self.right[node], target)
    else:
      if self.left[node] == 0:
        return self.right[node]
      if self.right[node] == 0:
        return self.left[node]
      successor = self.right[node]
      while self.left[successor]:
        successor = self.left[successor]
      self.key[node] = self.key[successor]
      self.right[node] = self._delete(self.right[node], self.key[successor])
    return self._rebalance(node)

  def arrays(self):
    return {"key": self.key, "left": self.left, "right": self.right,
            "ht": self.ht, "root": self.root, "nfree": self.nfree}
