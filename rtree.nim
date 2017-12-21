# plain draft of generic rtree
# S. Salewski, 21-DEC-2017

# http://www-db.deis.unibo.it/courses/SI-LS/papers/Gut84.pdf

# RT: range type like float, int
# D: Dimension
# M: Max entries in one node
# LT: leaf type

# https://irclogs.nim-lang.org/01-12-2017.html
# 23:05:48	Araq: just throw away this code, once it compiles, nobody can maintain it

type
  Dim* = static[int]
  Ext[RT] = tuple[a, b: RT] # extend (range) 
  Box*[D: Dim; RT] = array[D, Ext[RT]] # Rectangle for 2D
  L*[D: Dim; RT, LT] = tuple[b: Box[D, RT]; l: LT] # called Index Entry or index record in the Guttman paper
  H[M, D: Dim; RT, LT] = ref object of RootRef
    parent: H[M, D, RT, LT]
    numEntries: int
    level: int
  N[M, D: Dim; RT, LT] = tuple[b: Box[D, RT]; n: H[M, D, RT, LT]]
  LA[M, D: Dim; RT, LT] = array[M, L[D, RT, LT]]
  NA[M, D: Dim; RT, LT] = array[M, N[M, D, RT, LT]]
  Leaf[M, D: Dim; RT, LT] = ref object of H[M, D, RT, LT]
    a: LA[M, D, RT, LT]
  Node[M, D: Dim; RT, LT] = ref object of H[M, D, RT, LT]
    a: NA[M, D, RT, LT]
  RTree*[M, D: Dim; RT, LT] = ref object
    root: H[M, D, RT, LT]
    bigM: int
    m: int

proc newLeaf[M, D: Dim; RT, LT](): Leaf[M, D, RT, LT] =
  new result

proc newNode[M, D: Dim; RT, LT](): Node[M, D, RT, LT] =
  new result

proc newRTree*[M, D: Dim; RT, LT](nimFill: range[30 .. 50] = 40): RTree[M, D, RT, LT] =
  assert(M > 1 and M < 101)
  new result
  result.bigM = M
  result.m = M * nimFill div 100
  result.root = newLeaf[M, D, RT, LT]()

proc union(r1, r2: Box): Box =
  for i in 0 .. r1.high:
    result[i]. a = min(r1[i]. a, r2[i]. a)
    result[i]. b = max(r1[i]. b, r2[i]. b)

proc intersect(r1, r2: Box): bool =
  for i in 0 .. r1.high:
    if r1[i].b < r2[i].a or r1[i].a > r2[i].b:
      return false
  return true

proc area(r: Box): auto = #type(r[0].a) =
  result = type(r[0].a)(1)
  for i in 0 .. r.high:
    result *= r[i]. b - r[i]. a

# how much enlargement does r1 need to include r2
proc enlargement(r1, r2: Box): auto =
  area(union(r1, r2)) - area(r1)

proc search*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; b: Box[D, RT]): seq[LT] =
  proc s[M, D: Dim; RT, LT](n: H[M, D, RT, LT]; b: Box[D, RT]; res: var seq[LT]) =
    if n of Node[M, D, RT, LT]:
      let h = Node[M, D, RT, LT](n)
      for i in 0 ..< n.numEntries:
        if intersect(h.a[i].b, b):
          s(h.a[i].n, b, res)
    elif n of Leaf[M, D, RT, LT]:
      let h = Leaf[M, D, RT, LT](n)
      for i in 0 ..< n.numEntries:
        if intersect(h.a[i].b, b):
          res.add(h.a[i].l)
    else: assert false
  result = newSeq[LT]()
  s(t.root, b, result)

# Insertion
proc chooseLeaf[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; b: Box[D, RT]; level: int): H[M, D, RT, LT] =
  assert level >= 0
  var n = t.root
  while n.level > level:
    var j = -1 # selected index
    var x: type(b[0].a)
    let nn = Node[M, D, RT, LT](n)
    for i in 0 ..< n.numEntries:
      let h = enlargement(nn.a[i].b, b)
      if j < 0 or h < x or (x == h and area(nn.a[i].b) < area(nn.a[j].b)):
        x = h
        j = i
    n = nn.a[j].n
  return n

proc pickSeeds[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; n: Node[M, D, RT, LT] | Leaf[M, D, RT, LT]; bx: Box[D, RT]): (int, int) =
  var i0, j0: int
  var bi, bj: type(bx)
  var largestWaste = type(n.a[0].b[0].a).low
  for i in -1 .. n.a.high:
    for j in 0 .. n.a.high:
      if unlikely(i == j): continue
      if unlikely(i < 0):
        bi = bx
      else:
        bi = n.a[i].b
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
  for i in 1 ..< n1.numEntries:
    b1 = union(b1, n1.a[i].b)
  var b2 = n2.a[0].b
  for i in 1 ..< n2.numEntries:
    b2 = union(b2, n2.a[i].b)
  let a1 = area(b1)
  let a2 = area(b2)
  var d = type(a1).low
  for i in 0 ..< n0.numEntries:
    let d1 = area(union(b1, n0.a[i].b)) - a1
    let d2 = area(union(b2, n0.a[i].b)) - a2
    if abs(d1 - d2) > d:
      result = i
      d = abs(d1 - d2)

proc quadraticSplit[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; n: var Node[M, D, RT, LT] | var Leaf[M, D, RT, LT]; lx: L[D, RT, LT] | N[M, D, RT, LT]): type(n) =
  var n1, n2: type(n)
  var s1, s2: int
  new n1
  new n2
  n1.parent = n.parent
  n2.parent = n.parent
  n1.level = n.level
  n2.level = n.level
  (s1, s2) = pickSeeds(t, n, lx.b)
  assert s1 >= -1 and s2 >= 0
  if unlikely(s1 < 0):
    n1.a[0] = lx
  else:
    n1.a[0] = n.a[s1]
    dec(n.numEntries)
    if s2 ==  n.numEntries: # important fix
      s2 = s1
    n.a[s1] = n.a[n.numEntries]
  inc(n1.numEntries)
  var b1 = n1.a[0].b
  n2.a[0] = n.a[s2]
  dec(n.numEntries)
  n.a[s2] = n.a[n.numEntries]
  inc(n2.numEntries)
  var b2 = n2.a[0].b
  if s1 >= 0:
    n.a[n.numEntries] = lx
    inc(n.numEntries)
  while n.numEntries > 0 and n1.numEntries < (t.bigM + 1 - t.m) and n2.numEntries < (t.bigM + 1 - t.m):
    let next = pickNext(t, n, n1, n2)
    let d1 = area(union(b1, n.a[next].b)) - area(b1)
    let d2 = area(union(b2, n.a[next].b)) - area(b2)
    if (d1 < d2) or (d1 == d2 and ((area(b1) < area(b2)) or (area(b1) == area(b2) and n1.numEntries < n2.numEntries))):
      n1.a[n1.numEntries] = n.a[next]
      b1 = union(b1, n.a[next].b)
      inc(n1.numEntries)
    else:
      n2.a[n2.numEntries] = n.a[next]
      b2 = union(b2, n.a[next].b)
      inc(n2.numEntries)
    dec(n.numEntries)
    n.a[next] = n.a[n.numEntries]
  if n.numEntries == 0:
    discard
  elif n1.numEntries == (t.bigM + 1 - t.m):
    while n.numEntries > 0:
      dec(n.numEntries)
      n2.a[n2.numEntries] = n.a[n.numEntries]
      inc(n2.numEntries)
  elif n2.numEntries == (t.bigM + 1 - t.m):
    while n.numEntries > 0:
      dec(n.numEntries)
      n1.a[n1.numEntries] = n.a[n.numEntries]
      inc(n1.numEntries)
  when n is Node[M, D, RT, LT]:
    for i in 0 ..< n2.numEntries:
      n2.a[i].n.parent = n2
  n[] = n1[]
  return n2

proc adjustTree[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; l, ll: H[M, D, RT, LT]; hb: Box[D, RT]) =
  var n = l
  var nn = ll
  assert n != nil
  while true:
    if n == t.root:
      if nn == nil:
        break
      t.root = newNode[M, D, RT, LT]()
      t.root.level = n.level + 1
      Node[M, D, RT, LT](t.root).a[0].n = n
      n.parent = t.root
      nn.parent = t.root
      t.root.numEntries = 1
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
    if n of Leaf[M, D, RT, LT]:
      for j in 1 ..< n.numEntries:
        b = rtree.union(b, Leaf[M, D, RT, LT](n).a[j].b)
    elif n of Node[M, D, RT, LT]:
      for j in 1 ..< n.numEntries:
        b = union(b, Node[M, D, RT, LT](n).a[j].b)
    else:
      assert false
    p.a[i].b = b
    n = H[M, D, RT, LT](p)
    if nn != nil:
      if nn of Leaf[M, D, RT, LT]:
        b = Leaf[M, D, RT, LT](nn).a[0].b
      elif nn of Node[M, D, RT, LT]:
        b = Node[M, D, RT, LT](nn).a[0].b
      else:
        assert false
      if nn of Leaf[M, D, RT, LT]:
        for j in 1 ..< nn.numEntries:
          b = union(b, Leaf[M, D, RT, LT](nn).a[j].b)
      elif n of Node[M, D, RT, LT]:
        for j in 1 ..< nn.numEntries:
          b = union(b, Node[M, D, RT, LT](nn).a[j].b)
      else:
        assert false
      if p.numEntries < p.a.len:
        p.a[p.numEntries].b = b
        p.a[p.numEntries].n = nn
        inc(p.numEntries)
        assert n != nil
        nn = nil
      else:
        var h: N[M, D, RT, LT]
        h.b = b
        h.n = nn
        nn = quadraticSplit(t, p, h)
    assert n == H[M, D, RT, LT](p)
    assert n != nil
    assert t.root != nil

proc insertNode[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: N[M, D, RT, LT]; level: int) =
  assert level > 0
  let l = Node[M, D, RT, LT](chooseLeaf(t, leaf.b, level))
  if l.numEntries < l.a.len:
    l.a[l.numEntries] = leaf
    inc(l.numEntries)
    leaf.n.parent = l
    adjustTree(t, l, nil, leaf.b)
  else:
    let l2 = quadraticSplit(t, l, leaf)
    assert l2.level == l.level
    adjustTree(t, l, l2, leaf.b)

proc insert*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: L[D, RT, LT]) =
  for d in leaf.b:
    assert d.a <= d.b
  let l = Leaf[M, D, RT, LT](chooseLeaf(t, leaf.b, 0))
  if l.numEntries < l.a.len:
    l.a[l.numEntries] = leaf
    inc(l.numEntries)
    adjustTree(t, l, nil, leaf.b)
  else:
    let l2 = quadraticSplit(t, l, leaf)
    assert l2.level == l.level
    adjustTree(t, l, l2, leaf.b)

# delete
proc findLeaf[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: L[D, RT, LT]): Leaf[M, D, RT, LT] =
  proc fl[M, D: Dim; RT, LT](h: H[M, D, RT, LT]; leaf: L[D, RT, LT]): Leaf[M, D, RT, LT] =
    var n = h
    if n of Node[M, D, RT, LT]:
      for i in 0 ..< n.numEntries:
        if intersect(Node[M, D, RT, LT](n).a[i].b, leaf.b):
          let l = fl(Node[M, D, RT, LT](n).a[i].n, leaf)
          if l != nil:
            return l
    elif n of Leaf[M, D, RT, LT]:
      for i in 0 ..< n.numEntries:
        if Leaf[M, D, RT, LT](n).a[i].l == leaf.l:
          return Leaf[M, D, RT, LT](n)
    else:
      assert false
    return nil
  fl(t.root, leaf)

proc condenseTree[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: Leaf[M, D, RT, LT]) =
  var n: H[M, D, RT, LT] = leaf
  var q = newSeq[H[M, D, RT, LT]]()
  var b: type(leaf.a[0].b)
  while n != t.root:
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
      if n of Leaf[M, D, RT, LT]:
        for j in 1 ..< n.numEntries:
          b = union(b, Leaf[M, D, RT, LT](n).a[j].b)
      elif n of Node[M, D, RT, LT]:
        for j in 1 ..< n.numEntries:
          b = union(b, Node[M, D, RT, LT](n).a[j].b)
      else:
        assert false
      p.a[i].b = b
    n = n.parent
  for n in q:
    if n of Leaf[M, D, RT, LT]:
      for i in 0 ..< n.numEntries: 
        insert(t, Leaf[M, D, RT, LT](n).a[i])
    elif n of Node[M, D, RT, LT]:
      for i in 0 ..< n.numEntries: 
        insertNode(t, Node[M, D, RT, LT](n).a[i], n.level)
    else:
      assert false

proc delete*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: L[D, RT, LT]): bool {.discardable.} =
  let l = findLeaf(t, leaf)
  if l.isNil:
    return false
  else:
    var i = 0
    while l.a[i] != leaf:
      inc(i)
    dec(l.numEntries)
    l.a[i] = l.a[l.numEntries]
    condenseTree(t, l)
    if t.root.numEntries == 1:
      if t.root of Node[M, D, RT, LT]:
        t.root = Node[M, D, RT, LT](t.root).a[0].n
      t.root.parent = nil
    return true

when isMainModule:

  type
    RSE = L[2, int, int]
    RSeq = seq[RSE]

  proc rseq_search(rs: RSeq; rse: RSE): seq[int] =
    result = newSeq[int]() 
    for i in rs:
      if intersect(i.b, rse.b):
        result.add(i.l)

  proc rseq_delete(rs: var RSeq; rse: RSE): bool =
    for i in 0 .. rs.high:
      if rs[i] == rse:
        #rs.delete(i)
        rs[i] = rs[rs.high]
        rs.setLen(rs.len - 1)
        return true

  import random, algorithm

  proc test(n: int) =
    var b: Box[2, int]
    var x1, x2, y1, y2: int
    var t = newRTree[8, 2, int, int]()
    var rs = newSeq[RSE]()
    for i in 0 .. n - 1:
      x1 = rand(1000)
      y1 = rand(1000)
      x2 = x1 + rand(25)
      y2 = y1 + rand(25)
      b = [(x1, x2), (y1, y2)]
      let el: L[2, int, int] = (b, i)
      t.insert(el)
      rs.add(el)

    for i in 0 .. (n div 4):
      let j = rand(rs.high)
      var el = rs[j]
      assert t.delete(el)
      assert rs.rseq_delete(el)

    for i in 0 .. n - 1:
      x1 = rand(1000)
      y1 = rand(1000)
      x2 = x1 + rand(100)
      y2 = y1 + rand(100)
      b = [(x1, x2), (y1, y2)]
      let el: L[2, int, int] = (b, i)
      let r = search(t, b)
      let r2 = rseq_search(rs, el)
      assert r.len == r2.len
      assert r.sorted(system.cmp) == r2.sorted(system.cmp)

  test(999)

  # 422 lines


