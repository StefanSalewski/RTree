# plain completely untested draft of generic rtree
# S. Salewski, 08-DEC-2017

# http://www-db.deis.unibo.it/courses/SI-LS/papers/Gut84.pdf

# RT: range type like float, int
# D: Dimension
# M: Max entries in one node
# LT: leaf type

# https://irclogs.nim-lang.org/01-12-2017.html
# 23:04:33	Araq: N[D: Dim; RT] = tuple[b: Box[D, RT]; n: N[D, RT]] # requires an infinite amount of memory
# 23:05:48	Araq: just throw away this code, once it compiles, nobody can maintain it

type
  Dim = static[int]
  Ext[RT] = tuple[a, b: RT] # extend (range) 
  Box[D: Dim; RT] = array[D, Ext[RT]]
  L[D: Dim; RT, LT] = tuple[b: Box[D, RT]; l: LT] # called Index Entry or index record in the paper
  #N[D: Dim; RT] = tuple[b: Box[D, RT]; n: N[D, RT]] # TODO that generates infinite recursion as Araq confirmed.
  N[D: Dim; RT] = tuple[b: Box[D, RT]; n: RootRef] # TODO
  LA[M, D: Dim; RT, LT] = array[M, L[D, RT, LT]]
  NA[M, D: Dim; RT] = array[M, N[D, RT]]
  H[M, D: Dim; RT, LT] = ref object of RootRef
    parent: H[M, D, RT, LT]
    numEntries: int
    level: int
  Leaf[M, D: Dim; RT, LT] = ref object of H[M, D, RT, LT]
    a: LA[M, D, RT, LT]
  Node[M, D: Dim; RT, LT] = ref object of H[M, D, RT, LT]
    a: NA[M, D, RT]
  RTree[M, D: Dim; RT, LT] = ref object
    root: H[M, D, RT, LT]
    bigM: int
    m: int

proc newLeaf[M, D: Dim; RT, LT](): Leaf[M, D, RT, LT] =
  new result

proc newNode[M, D: Dim; RT, LT](): Node[M, D, RT, LT] =
  new result

proc newRTree[M, D: Dim; RT, LT](): RTree[M, D, RT, LT] =
  new result
  result.bigM = M
  result.m = M * 40 div 100
  result.root = newLeaf[M, D, RT, LT]()
  assert result.root of Leaf[M, D, RT, LT]

proc union(r1, r2: Box): Box =
  for i in 0 .. r1.high:
    result[i]. a = min(r1[i]. a, r2[i]. a)
    result[i]. b = max(r1[i]. b, r2[i]. b)

proc intersect(r1, r2: Box): bool =
  for i in 0 .. r1.high:
    if r1[i].b < r2[i].a or r1[i].a > r2[i].b:
      return false
  return true

proc area(r: Box): auto =
  result = 1
  for i in 0 .. r.high:
    result *= r[i]. b - r[i]. a

# how much enlargement does r1 need to include r2
proc enlargement(r1, r2: Box): auto =
  area(union(r1, r2)) - area(r1)

proc search[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; b: Box[D, RT]): seq[LT] =
  proc s[M, D: Dim; RT, LT](n: H[M, D, RT, LT]; b: Box[D, RT]; res: var seq[LT]) =
    if n of Node[M, D, RT, LT]:
      for i in 0 ..< n.numEntries:
        if intersect(Node[M, D, RT, LT](n).a[i].b, b):
          s(H[M, D, RT, LT](Node[M, D, RT, LT](n).a[i].n), b, res)
    elif n of Leaf[M, D, RT, LT]:
      for i in 0 ..< n.numEntries:
        if intersect(Leaf[M, D, RT, LT](n).a[i].b, b):
          res.add(Leaf[M, D, RT, LT](n).a[i].l)
    else: assert false
  result = newSeq[LT]()
  s(t.root, b, result)

# Insertion
proc chooseLeaf[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; b: Box[D, RT]; level: int): H[M, D, RT, LT] =
  var n = t.root
  while n is Node and n.level > level:
    var j = -1 # selected index
    var x: type(b[0].a)
    for i in 0 ..< n.numEntries:
      let h = enlargement(Node[M, D, RT, LT](n).a[i].b, b)
      if j < 0 or h < x or (x == h and area(Node[M, D, RT, LT](n).a[i].b) < area(Node[M, D, RT, LT](n).a[j].b)):
        x = h
        j = i
    n = Node[M, D, RT, LT](Node[M, D, RT, LT](n).a[j].n)
  assert n of Leaf[M, D, RT, LT]
  return H[M, D, RT, LT](n)

proc pickSeeds[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; n: Node[M, D, RT, LT] | Leaf[M, D, RT, LT]; bx: Box[D, RT]): (int, int) =
  var i0, j0: int
  var bi, bj: type(bx)
  var largestWaste = type(n.a[0].b[0].a).low
  for i in -1 .. n.a.high:
    for j in -1 .. n.a.high:
      if i == j: continue
      if i == -1:
        bi = bx
      else:
        bi = n.a[i].b
      if j == -1:
        bj = bx
      else:
        bj = n.a[j].b
      let b = union(bi, bj)
      let h = area(b) - area(bi) - area(bj)
      if h > largestWaste:
        largestWaste = h
        i0 = i
        j0 = j
  return (i0, j0)

proc pickNext[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; n0, n1, n2: Node[M, D, RT, LT] | Leaf[M, D, RT, LT]): int =
  var b1 = n1.a[0].b
  for i in 1 .. n1.a.high:
    b1 = union(b1, n1.a[i].b)
  var b2 = n2.a[0].b
  for i in 1 .. n2.a.high:
    b2 = union(b2, n2.a[i].b)
  let a1 = area(b1)
  let a2 = area(b2)
  var d = type(a1).low
  for i, n in n0.a:
    let d1 = area(union(b1, n.b)) - a1
    let d2 = area(union(b2, n.b)) - a2
    if i == 0 or abs(d1 - d2) > d:
      result = i
      d = abs(d1 - d2)

proc quadraticSplit[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; n: Node[M, D, RT, LT] | Leaf[M, D, RT, LT]; lx: L[D, RT, LT] | N[D, RT]): (type(n), type(n)) =
  var n1, n2: type(n)
  var s1, s2: int
  new n1
  new n2
  (s1, s2) = pickSeeds(t, n, lx.b)
  if s1 == -1:
    n1.a[0] = lx
  else:
    n1.a[0] = n.a[s1]
    dec(n.numEntries)
    n.a[s1] = n.a[n.numEntries]
  inc(n1.numEntries)
  var b1 = n1.a[0].b
  if s2 == -1:
    n2.a[0] = lx
  else:
    n2.a[0] = n.a[s2]
    dec(n.numEntries)
    n.a[s2] = n.a[n.numEntries]
  inc(n2.numEntries)
  var b2 = n2.a[0].b
  while n.numEntries > 0 and n1.numEntries < (t.bigM + 1 - t.m) and n2.numEntries < (t.bigM + 1 - t.m):
    let next = pickNext(t, n, n1, n2)
    let d1 = area(union(b1, n.a[next].b)) - area(b1)
    let d2 = area(union(b2, n.a[next].b)) - area(b2)
    if d1 < d2:
      n1.a[n1.numEntries] = n.a[next]
      b1 = union(b1, n.a[next].b)
      inc(n1.numEntries)
    else:
      n2.a[n2.numEntries] = n.a[next]
      b2 = union(b2, n.a[next].b)
      inc(n2.numEntries)
    n.a[next] = n.a[n.numEntries]
    dec(n.numEntries)
  if n1.numEntries == (t.bigM + 1 - t.m):
    while n.numEntries > 0:
      dec(n.numEntries)
      n2.a[n2.numEntries] = n.a[n.numEntries]
      inc(n2.numEntries)
  else:
    while n.numEntries > 0:
      dec(n.numEntries)
      n1.a[n1.numEntries] = n.a[n.numEntries]
      inc(n1.numEntries)
  return (n1, n2)

proc adjustTree[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; l, ll: H[M, D, RT, LT]; hb: Box[D, RT]) =
  var n = l
  var nn = ll
  while H[M, D, RT, LT](n) != t.root:
    let p = Node[M, D, RT, LT](n.parent)
    var i = 0
    while p.a[i].n != n:
      inc(i)
    var b: type(p.a[0].b)
    if n of Leaf[M, D, RT, LT]:
      b = Leaf[M, D, RT, LT](n).a[0].b
    elif n of Node[M, D, RT, LT]:
      b = Node[M, D, RT, LT](n).a[0].b
    else:
      assert false
    for j in 1 ..< n.numEntries:
      if n of Leaf[M, D, RT, LT]:
        b = union(b, Leaf[M, D, RT, LT](n).a[j].b)
      elif n of Node[M, D, RT, LT]:
        b = union(b, Node[M, D, RT, LT](n).a[j].b)
      else:
        assert false
    p.a[i].b = b
    if nn != nil:
      if nn of Leaf[M, D, RT, LT]:
        b = Leaf[M, D, RT, LT](nn).a[0].b
      elif nn of Node[M, D, RT, LT]:
        b = Node[M, D, RT, LT](nn).a[0].b
      else:
        assert false
      for j in 1 ..< nn.numEntries:
        if nn of Leaf[M, D, RT, LT]:
          b = union(b, Leaf[M, D, RT, LT](nn).a[j].b)
        elif n of Node[M, D, RT, LT]:
          b = union(b, Node[M, D, RT, LT](nn).a[j].b)
        else:
          assert false
      if p.numEntries < p.a.len:
        p.a[p.numEntries].b = b
        p.a[p.numEntries].n = nn
        inc(p.numEntries)
        n = H[M, D, RT, LT](n.parent)
        nn = nil
      else:
        var h: N[D, RT]
        h.b = b
        h.n = nn
        (n, nn) = quadraticSplit(t, p, h)
 
proc insertNode[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: N[D, RT]; level = 0) =
  let l = Node[M, D, RT, LT](chooseLeaf(t, leaf.b, level))
  if l.numEntries < l.a.len:
    l.a[l.numEntries] = leaf
    inc(l.numEntries)
    adjustTree(t, l, nil, leaf.b)
  else:
    var l1, l2: Node[M, D, RT, LT]
    (l1, l2) = quadraticSplit(t, l, leaf)
    adjustTree(t, l1, l2, leaf.b)
    if l == Node[M, D, RT, LT](t.root):
      t.root = newNode[M, D, RT, LT]()
      Node[M, D, RT, LT](t.root).a[0].n = l1
      Node[M, D, RT, LT](t.root).a[1].n = l2
      t.root.numEntries = 2

proc insert[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: L[D, RT, LT]; level = 0) =
  let l = Leaf[M, D, RT, LT](chooseLeaf(t, leaf.b, level))
  if l.numEntries < l.a.len:
    l.a[l.numEntries] = leaf
    inc(l.numEntries)
    adjustTree(t, l, nil, leaf.b)
  else:
    var l1, l2: Leaf[M, D, RT, LT]
    (l1, l2) = quadraticSplit(t, l, leaf)
    adjustTree(t, l1, l2, leaf.b)
    if l == Leaf[M, D, RT, LT](t.root):
      t.root = newNode[M, D, RT, LT]()
      Node[M, D, RT, LT](t.root).a[0].n = l1
      Node[M, D, RT, LT](t.root).a[1].n = l2
      t.root.numEntries = 2

# delete
proc findLeaf[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: L[D, RT, LT]): Leaf[M, D, RT, LT] =
  proc fl[M, D: Dim; RT, LT](h: H[M, D, RT, LT]; leaf: L[D, RT, LT]): Leaf[M, D, RT, LT] =
    var n = h
    if n is Node:
      for i in 0 ..< n.numEntries:
        if intersect(Node[M, D, RT, LT](n).a[i].b, leaf.b):
          let l = fl(H[M, D, RT, LT](Node[M, D, RT, LT](n).a[i].n), leaf)
          if l != nil:
            return l
    else:
      for i in 0 ..< n.numEntries:
        if Leaf[M, D, RT, LT](n).a[i].l == leaf.l:
          return Leaf[M, D, RT, LT](n)
    return nil
  fl(t.root, leaf)

proc condenseTree[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: Leaf[M, D, RT, LT]) =
  var n: H[M, D, RT, LT] = leaf
  var q = newSeq[H[M, D, RT, LT]]()
  var b: type(leaf.a[0].b)
  while H[M, D, RT, LT](n) != t.root:
    let p = Node[M, D, RT, LT](n.parent)
    var i = 0
    while p.a[i].n != n:
      inc(i)
    if n.numEntries < t.m:
      dec(p.numEntries)
      p.a[i] = p.a[p.numEntries]
      q.add(n)
    else:
      if n of Leaf[M, D, RT, LT]:
        b = Leaf[M, D, RT, LT](n).a[0].b
      elif n of Node[M, D, RT, LT]:
        b = Node[M, D, RT, LT](n).a[0].b
      else:
        assert false
      for j in 1 ..< n.numEntries:
        if n of Leaf[M, D, RT, LT]:
          b = union(b, Leaf[M, D, RT, LT](n).a[j].b)
        elif n of Node[M, D, RT, LT]:
          b = union(b, Node[M, D, RT, LT](n).a[j].b)
        else:
          assert false
      p.a[i].b = b
    n = n.parent
  for j in 0 .. q.high:
    let n = q[j]
    if n of Leaf[M, D, RT, LT]:
      for i in Leaf[M, D, RT, LT](n).a:
        insert(t, i)
    elif n of Node[M, D, RT, LT]:
      for i in Node[M, D, RT, LT](n).a:
        insertNode(t, i, n.level)
    else:
      assert false

proc delete[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: L[D, RT, LT]) =
  let l = findLeaf(t, leaf)
  if l != nil:
    var i = 0
    while L[D, RT, LT](l.a[i]) != leaf:
      inc(i)
    dec(l.numEntries)
    l.a[i] = l.a[l.numEntries]
    condenseTree(t, l)
    if t.root.numEntries == 1:
      t.root = H[M, D, RT, LT](Node[M, D, RT, LT](t.root).a[0].n) 

var m, n: Box[2, int]

m[0].a = 1
m[0].b = 2
m[1].a = 5
m[1].b = 7

n = [(a: 2, b: 3), (a: 3, b: 6)]

var ix: L[2, int, int] = (m, 7)

var t = newRTree[50, 2, int, int]()

insert(t, ix)
#delete(t, ix)
 
let r = search(t, m)

echo r.len
echo r[0]


