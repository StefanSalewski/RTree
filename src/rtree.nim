# Nim RTree and R*Tree implementation
# (c) S. Salewski 2018
# 2018-JAN-06 -- initial release
# 2019-OCT-14 -- added nearest neighbor search and TGS bulk loading
# 2021-JAN-08 -- added items() iterator

# http://www-db.deis.unibo.it/courses/SI-LS/papers/Gut84.pdf # original R-Tree by Guttman
# http://dbs.mathematik.uni-marburg.de/publications/myPapers/1990/BKSS90.pdf # improved R*-Tree
# http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.386.8193&rep=rep1&type=pdf # inc. k nearest neighbor search
# http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.20.9245&rep=rep1&type=pdf # sketch of TGS bulk loading 
# http://www.cs.umd.edu/~hjs/pubs/AlborziIPL07.pdf # detailed algorithm of TGS bulk loading

# RT: range type like float, int
# D: Dimension
# M: Max entries in one node
# LT: leaf type

type
  Dim* = static[int]
  Ext*[RT] = tuple[a, b: RT] # extend (range) # export only for docs
  Box*[D: Dim; RT] = array[D, Ext[RT]] # Rectangle for 2D
  BoxCenter*[D: Dim; RT] = array[D, RT]
  L*[D: Dim; RT, LT] = tuple[b: Box[D, RT]; l: LT] # called Index Entry or index record in the Guttman paper
  LTGS[D: Dim; RT, LT] = tuple[b: Box[D, RT]; l: LT; tgsID: int] # we need unique id for bulk loading

  RTRef[RT] = ref object of RootRef # we need pri field for nearest neighbor search
    pri: RT

  H[M, D: Dim; RT, LT] = ref object of RTRef[RT]
    parent: H[M, D, RT, LT]
    numEntries: int
    cur: int # for iteration
    level: int
  N[M, D: Dim; RT, LT] = tuple[b: Box[D, RT]; n: H[M, D, RT, LT]]
  LA[M, D: Dim; RT, LT] = array[M, L[D, RT, LT]]
  NA[M, D: Dim; RT, LT] = array[M, N[M, D, RT, LT]]
  Leaf[M, D: Dim; RT, LT] = ref object of H[M, D, RT, LT]
    a: LA[M, D, RT, LT]
  Node[M, D: Dim; RT, LT] = ref object of H[M, D, RT, LT]
    a: NA[M, D, RT, LT]

  RTree*[M, D: Dim; RT, LT] = ref object of RootRef
    root: H[M, D, RT, LT]
    bigM: int
    m: int

  RStarTree*[M, D: Dim; RT, LT] = ref object of RTree[M, D, RT, LT]
    firstOverflow: array[32, bool]
    p: int

#[
proc boxIsValid(r: Box): bool =
  for i in 0 .. r1.high:
    if r[i].b < r[i].a:
      return false
  return true
]#

proc newLeaf[M, D: Dim; RT, LT](): Leaf[M, D, RT, LT] =
  new result

proc newNode[M, D: Dim; RT, LT](): Node[M, D, RT, LT] =
  new result

proc newRTree*[M, D: Dim; RT, LT](minFill: range[30 .. 50] = 40): RTree[M, D, RT, LT] =
  assert(M > 1 and M < 101)
  new result
  result.bigM = M
  result.m = max(1, M * minFill div 100)
  assert(0 < result.m and result.m <= M div 2)
  result.root = newLeaf[M, D, RT, LT]()

proc newRStarTree*[M, D: Dim; RT, LT](minFill: range[30 .. 50] = 40): RStarTree[M, D, RT, LT] =
  # NOTE: 2 <= m <= M/2 # page 323
  assert(M > 3 and M < 101)
  new result
  result.bigM = M 
  result.m = max(2, M * minFill div 100)
  assert(1 < result.m and result.m <= M div 2)
  result.root = newLeaf[M, D, RT, LT]()
  result.p = M * 30 div 100 # for reinsert: remove the first p entries...
  assert(result.p > 0)

proc center(r: Box): auto = #BoxCenter[r.len, type(r[0].a)] =
  var result: BoxCenter[r.len, type(r[0].a)]
  for i in 0 .. r.high:
    when r[0].a is SomeInteger:
      result[i] = (r[i].a + r[i].b) div 2
    elif r[0].a is SomeFloat:
      result[i] = (r[i].a + r[i].b) * 0.5
    else: assert false
  return result

proc distance(c1, c2: BoxCenter): auto = # squared!
#proc distance(c1, c2: BoxCenter): type(c1[0]) =
  var result: type(c1[0])
  for i in 0 .. c1.high:
    result += (c1[i] - c2[i]) * (c1[i] - c2[i])
  return result

proc overlap(r1, r2: Box): auto =
  result = type(r1[0].a)(1)
  for i in 0 .. r1.high:
    result *= (min(r1[i].b, r2[i].b) - max(r1[i].a, r2[i].a))
    if result <= 0: return 0

proc union(r1, r2: Box): Box =
  for i in 0 .. r1.high:
    result[i].a = min(r1[i].a, r2[i].a)
    result[i].b = max(r1[i].b, r2[i].b)

proc intersect(r1, r2: Box): bool =
  for i in 0 .. r1.high:
    if r1[i].b < r2[i].a or r1[i].a > r2[i].b:
      return false
  return true

proc area(r: Box): auto = #type(r[0].a) =
  result = type(r[0].a)(1)
  for i in 0 .. r.high:
    result *= r[i].b - r[i].a

proc margin(r: Box): auto = #type(r[0].a) =
  result = type(r[0].a)(0)
  for i in 0 .. r.high:
    result += r[i].b - r[i].a

# how much enlargement does r1 need to include r2
proc enlargement(r1, r2: Box): auto =
  area(union(r1, r2)) - area(r1)

proc search*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; b: Box[D, RT]): seq[L[D, RT, LT]] =
  for d in b:
    assert d.a <= d.b
  proc s[M, D: Dim; RT, LT](n: H[M, D, RT, LT]; b: Box[D, RT]; res: var seq[L[D, RT, LT]]) =
    if n of Node[M, D, RT, LT]:
      let h = Node[M, D, RT, LT](n)
      for i in 0 ..< n.numEntries:
        if intersect(h.a[i].b, b):
          s(h.a[i].n, b, res)
    elif n of Leaf[M, D, RT, LT]:
      let h = Leaf[M, D, RT, LT](n)
      for i in 0 ..< n.numEntries:
        if intersect(h.a[i].b, b):
          res.add(h.a[i])
    else: assert false
  # result = newSeq[L[D, RT, LT]]() # we should not need this in Nim > v1.0
  s(t.root, b, result)

proc searchObj*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; b: Box[D, RT]): seq[LT] =
  for d in b:
    assert d.a <= d.b
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
  # result = newSeq[LT]() # we should not need this in Nim > v1.0
  s(t.root, b, result)

# Insertion
# a R*Tree proc
proc chooseSubtree[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; b: Box[D, RT]; level: int): H[M, D, RT, LT] =
  assert level >= 0
  var n = t.root
  while n.level > level:
    let nn = Node[M, D, RT, LT](n)
    var i0 = 0 # selected index
    var minLoss = type(b[0].a).high
    if n.level == 1: # childreen are leaves -- determine the minimum overlap costs
      for i in 0 ..< n.numEntries:
        let nx = union(nn.a[i].b, b)
        var loss: RT # = 0
        for j in 0 ..< n.numEntries:
          if i == j: continue
          loss += (overlap(nx, nn.a[j].b) - overlap(nn.a[i].b, nn.a[j].b)) # overlap (i, j) == (j, i), so maybe cache that?
        var rep = loss < minLoss
        if loss == minLoss:
          let l2 = enlargement(nn.a[i].b, b) - enlargement(nn.a[i0].b, b)
          rep = l2 < 0
          if l2 == 0:
            let l3 = area(nn.a[i].b) - area(nn.a[i0].b)
            rep = l3 < 0
            if l3 == 0:
              rep = nn.a[i].n.numEntries < nn.a[i0].n.numEntries
        if rep:
          i0 = i
          minLoss = loss
    else:
      for i in 0 ..< n.numEntries:
        let loss = enlargement(nn.a[i].b, b)
        var rep = loss < minLoss
        if loss == minLoss:
          let l3 = area(nn.a[i].b) - area(nn.a[i0].b)
          rep = l3 < 0
          if l3 == 0:
            rep = nn.a[i].n.numEntries < nn.a[i0].n.numEntries
        if rep:
          i0 = i
          minLoss = loss
    n = nn.a[i0].n
  return n

#[
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
]#

proc pickSeeds[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; n: Node[M, D, RT, LT] | Leaf[M, D, RT, LT]; bx: Box[D, RT]): (int, int) =
  var i0, j0: int
  var bi, bj: type(bx)
  var largestWaste = type(bx[0].a).low
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

proc pickNext[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; n0, n1, n2: Node[M, D, RT, LT] | Leaf[M, D, RT, LT]; b1, b2: Box[D, RT]): int =
  let a1 = area(b1)
  let a2 = area(b2)
  var d = type(a1).low
  for i in 0 ..< n0.numEntries:
    let d1 = area(union(b1, n0.a[i].b)) - a1
    let d2 = area(union(b2, n0.a[i].b)) - a2
    if (d1 - d2) * (d1 - d2) > d:
      result = i
      d = (d1 - d2) * (d1 - d2)

from algorithm import SortOrder, sort
proc sortPlus[T](a: var openArray[T]; ax: var T; cmp: proc (x, y: T): int {.closure.}; order = algorithm.SortOrder.Ascending) =
  var j = 0
  let sign = if order == algorithm.SortOrder.Ascending: 1 else: -1
  for i in 1 .. a.high:
    if cmp(a[i], a[j]) * sign < 0:
      j = i
  if cmp(a[j], ax) * sign < 0:
    swap(ax, a[j])
  a.sort(cmp, order)

# R*Tree procs
proc rstarSplit[M, D: Dim; RT, LT](t: RStarTree[M, D, RT, LT]; n: var Node[M, D, RT, LT] | var Leaf[M, D, RT, LT]; lx: L[D, RT,
    LT] | N[M, D, RT, LT]): type(n) =
  type NL = type(lx)
  var nBest: type(n)
  new nBest
  var lx = lx
  when n is Node[M, D, RT, LT]:
    lx.n.parent = n
  var lxbest: type(lx)
  when RT is float:
    var m0 = system.Inf
  elif RT is float32:
    var m0 = 1e30 # ugly
  else:
    var m0 = lx.b[0].a.high
  for d2 in 0 ..< 2 * D:
    let d = d2 div 2
    if d2 mod 2 == 0:
      sortPlus(n.a, lx, proc (x, y: NL): int = cmp(x.b[d].a, y.b[d].a))
    else:
      sortPlus(n.a, lx, proc (x, y: NL): int = cmp(x.b[d].b, y.b[d].b))
    for i in t.m - 1 .. n.a.high - t.m + 1:
      var b = lx.b
      for j in 0 ..< i: # we can precalculate union() for range 0 .. t.m - 1, but that seems to give no real benefit. Maybe for very large M?
        b = union(n.a[j].b, b)
      var m = margin(b)
      b = n.a[^1].b
      for j in i ..< n.a.high: # again, precalculation of tail would be possible
        b = union(n.a[j].b, b)
      m += margin(b)
      if m < m0:
        nbest[] = n[]
        lxbest = lx
        m0 = m
  var i0 = -1
  #var o0 = lx.b[0].a.high
  when RT is float:
    var o0 = system.Inf
  elif RT is float32:
    var o0 = 1e30 # ugly
  else:
    var o0 = lx.b[0].a.high
  for i in t.m - 1 .. n.a.high - t.m + 1:
    var b1 = lxbest.b
    for j in 0 ..< i:
      b1 = union(nbest.a[j].b, b1)
    var b2 = nbest.a[^1].b
    for j in i ..< n.a.high:
      b2 = union(nbest.a[j].b, b2)
    let o = overlap(b1, b2)
    if o < o0:
      i0 = i
      o0 = o
  n.a[0] = lxbest
  for i in 0 ..< i0:
    n.a[i + 1] = nbest.a[i]
  new result
  result.level = n.level
  result.parent = n.parent
  for i in i0 .. n.a.high:
    result.a[i - i0] = nbest.a[i]
  n.numEntries = i0 + 1
  result.numEntries = M - i0
  when n is Node[M, D, RT, LT]:
    for i in 0 ..< result.numEntries:
      result.a[i].n.parent = result

proc quadraticSplit[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; n: var Node[M, D, RT, LT] | var Leaf[M, D, RT, LT]; lx: L[D, RT,
    LT] | N[M, D, RT, LT]): type(n) =
  var n1, n2: type(n)
  var s1, s2: int
  new n1
  new n2
  n1.parent = n.parent
  n2.parent = n.parent
  n1.level = n.level
  n2.level = n.level
  var lx = lx
  when n is Node[M, D, RT, LT]:
    lx.n.parent = n
  (s1, s2) = pickSeeds(t, n, lx.b)
  assert s1 >= -1 and s2 >= 0
  if unlikely(s1 < 0):
    n1.a[0] = lx
  else:
    n1.a[0] = n.a[s1]
    dec(n.numEntries)
    if s2 == n.numEntries: # important fix
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
    let next = pickNext(t, n, n1, n2, b1, b2)
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

proc overflowTreatment[M, D: Dim; RT, LT](t: RStarTree[M, D, RT, LT]; n: var Node[M, D, RT, LT] | var Leaf[M, D, RT, LT]; lx: L[D,
    RT, LT] | N[M, D, RT, LT]): type(n)

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
      when false: #if likely(nn.isNil): # no performance gain
        b = union(p.a[i].b, Leaf[M, D, RT, LT](n).a[n.numEntries - 1].b)
      else:
        b = Leaf[M, D, RT, LT](n).a[0].b
        for j in 1 ..< n.numEntries:
          b = rtree.union(b, Leaf[M, D, RT, LT](n).a[j].b)
    elif n of Node[M, D, RT, LT]:
      b = Node[M, D, RT, LT](n).a[0].b
      for j in 1 ..< n.numEntries:
        b = union(b, Node[M, D, RT, LT](n).a[j].b)
    else:
      assert false
    #if nn.isNil and p.a[i].b == b: break # no performance gain
    p.a[i].b = b
    n = H[M, D, RT, LT](p)
    if unlikely(nn != nil):
      if nn of Leaf[M, D, RT, LT]:
        b = Leaf[M, D, RT, LT](nn).a[0].b
        for j in 1 ..< nn.numEntries:
          b = union(b, Leaf[M, D, RT, LT](nn).a[j].b)
      elif nn of Node[M, D, RT, LT]:
        b = Node[M, D, RT, LT](nn).a[0].b
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
        let h: N[M, D, RT, LT] = (b, nn)
        if t of RStarTree[M, D, RT, LT]:
          nn = overflowTreatment(RStarTree[M, D, RT, LT](t), p, h)
        elif t of RTree[M, D, RT, LT]:
          nn = quadraticSplit(t, p, h)
        else:
          assert false
    assert n == H[M, D, RT, LT](p)
    assert n != nil
    assert t.root != nil

proc insert*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: N[M, D, RT, LT] | L[D, RT, LT]; level: int = 0) =
  when leaf is N[M, D, RT, LT]:
    assert level > 0
    type NodeLeaf = Node[M, D, RT, LT]
  else:
    assert level == 0
    type NodeLeaf = Leaf[M, D, RT, LT]
  for d in leaf.b:
    assert d.a <= d.b
  let l = NodeLeaf(chooseSubtree(t, leaf.b, level))
  if l.numEntries < l.a.len:
    l.a[l.numEntries] = leaf
    inc(l.numEntries)
    when leaf is N[M, D, RT, LT]:
      leaf.n.parent = l
    adjustTree(t, l, nil, leaf.b)
  else:
    let l2 = quadraticSplit(t, l, leaf)
    assert l2.level == l.level
    adjustTree(t, l, l2, leaf.b)

# R*Tree insert procs
proc rsinsert[M, D: Dim; RT, LT](t: RStarTree[M, D, RT, LT]; leaf: N[M, D, RT, LT] | L[D, RT, LT]; level: int)

proc reInsert[M, D: Dim; RT, LT](t: RStarTree[M, D, RT, LT]; n: var Node[M, D, RT, LT] | var Leaf[M, D, RT, LT]; lx: L[D, RT,
    LT] | N[M, D, RT, LT]) =
  type NL = type(lx)
  var lx = lx
  var buf: type(n.a) # well, lower elements are newer used
  let p = Node[M, D, RT, LT](n.parent)
  var i = 0
  while p.a[i].n != n:
    inc(i)
  let c = center(p.a[i].b)
  sortPlus(n.a, lx, proc (x, y: NL): int = cmp(distance(center(x.b), c), distance(center(y.b), c)))
  n.numEntries = M - t.p
  swap(n.a[n.numEntries], lx)
  inc n.numEntries
  var b = n.a[0].b
  for i in 1 ..< n.numEntries:
    b = union(b, n.a[i].b)
  p.a[i].b = b
  for i in M - t.p + 1 .. n.a.high:
    buf[i] = n.a[i]
  rsinsert(t, lx, n.level)
  for i in M - t.p + 1 .. n.a.high:
    rsinsert(t, buf[i], n.level)

proc overflowTreatment[M, D: Dim; RT, LT](t: RStarTree[M, D, RT, LT]; n: var Node[M, D, RT, LT] | var Leaf[M, D, RT, LT]; lx: L[D,
    RT, LT] | N[M, D, RT, LT]): type(n) =
  if n.level != t.root.level and t.firstOverflow[n.level]:
    t.firstOverflow[n.level] = false
    reInsert(t, n, lx)
    return nil
  else:
    let l2 = rstarSplit(t, n, lx)
    assert l2.level == n.level
    return l2

proc rsinsert[M, D: Dim; RT, LT](t: RStarTree[M, D, RT, LT]; leaf: N[M, D, RT, LT] | L[D, RT, LT]; level: int) =
  when leaf is N[M, D, RT, LT]:
    assert level > 0
    type NodeLeaf = Node[M, D, RT, LT]
  else:
    assert level == 0
    type NodeLeaf = Leaf[M, D, RT, LT]
  let l = NodeLeaf(chooseSubtree(t, leaf.b, level))
  if l.numEntries < l.a.len:
    l.a[l.numEntries] = leaf
    inc(l.numEntries)
    when leaf is N[M, D, RT, LT]:
      leaf.n.parent = l
    adjustTree(t, l, nil, leaf.b)
  else:
    when leaf is N[M, D, RT, LT]: # TODO do we need this?
      leaf.n.parent = l
    let l2 = overflowTreatment(t, l, leaf)
    if l2 != nil:
      assert l2.level == l.level
      adjustTree(t, l, l2, leaf.b)

proc insert*[M, D: Dim; RT, LT](t: RStarTree[M, D, RT, LT]; leaf: L[D, RT, LT]) =
  for d in leaf.b:
    assert d.a <= d.b
  for i in mitems(t.firstOverflow):
    i = true
  rsinsert(t, leaf, 0)

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
        if Leaf[M, D, RT, LT](n).a[i] == leaf:
          return Leaf[M, D, RT, LT](n)
    else:
      assert false
    return nil
  fl(t.root, leaf)

proc condenseTree[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; leaf: Leaf[M, D, RT, LT]) =
  var n: H[M, D, RT, LT] = leaf
  var q: seq[H[M, D, RT, LT]]
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
        for j in 1 ..< n.numEntries:
          b = union(b, Leaf[M, D, RT, LT](n).a[j].b)
      elif n of Node[M, D, RT, LT]:
        b = Node[M, D, RT, LT](n).a[0].b
        for j in 1 ..< n.numEntries:
          b = union(b, Node[M, D, RT, LT](n).a[j].b)
      else:
        assert false
      p.a[i].b = b
    n = n.parent
  if t of RStarTree[M, D, RT, LT]:
    for n in q:
      if n of Leaf[M, D, RT, LT]:
        for i in 0 ..< n.numEntries:
          for i in mitems(RStarTree[M, D, RT, LT](t).firstOverflow):
            i = true
          rsinsert(RStarTree[M, D, RT, LT](t), Leaf[M, D, RT, LT](n).a[i], 0)
      elif n of Node[M, D, RT, LT]:
        for i in 0 ..< n.numEntries:
          for i in mitems(RStarTree[M, D, RT, LT](t).firstOverflow):
            i = true
          rsinsert(RStarTree[M, D, RT, LT](t), Node[M, D, RT, LT](n).a[i], n.level)
      else:
        assert false
  elif t of RTree[M, D, RT, LT]:
    for n in q:
      if n of Leaf[M, D, RT, LT]:
        for i in 0 ..< n.numEntries:
          insert(t, Leaf[M, D, RT, LT](n).a[i])
      elif n of Node[M, D, RT, LT]:
        for i in 0 ..< n.numEntries:
          insert(t, Node[M, D, RT, LT](n).a[i], n.level)
      else:
        assert false
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

# TGS bulk loading
# http://www.cs.umd.edu/~hjs/pubs/AlborziIPL07.pdf
from math import `^`, ceil, log
from algorithm import sorted

# const NumTgsSortKeys[D: Dim] = 2 * D # generic constants do not work

const TgsX = 2 # for each dim we use left and right side of rectangle as sort key.
               #const TgsX = 3 # use left and right side of rectangle as sort key, additional use center.
               # total number of sort orderings is D * TgsX

type
  TgsSortKey[RT] = object # if k is equal for two objects, sort by idd for uniqe order
    k: RT
    idd: int
    first: int            # size of first seq when splitting

proc tgsCmp[RT](a, b: TgsSortKey[RT]): int =
  if a.k < b.k:
    -1
  elif a.k > b.k:
    1
  else:
    a.idd - b.idd

proc `<`[RT](a, b: TgsSortKey[RT]): bool = tgsCmp(a, b) < 0

proc tgsSortKey[D: Dim; RT, LT](el: LTGS[D, RT, LT]; s: int): TgsSortKey[RT] =
  assert(s >= 0 and s < TgsX * D) # s is the total number of sort oderings
  result.idd = el.tgsID
  when TgsX == 2:
    # assert(TgsX == 2)
    let i = s shr 1 # s div TgsX
    let j = s and 1 # s mod TgsX
    if j == 0:
      result.k = el.b[i].a
    else:
      result.k = el.b[i].b
  elif TgsX == 3: # sorting by center makes not much sense, we may never use this
    # assert(TgsX == 3)
    let i = s div TgsX
    let j = s mod TgsX
    case j
    of 0: result.k = el.b[i].a
    of 1: result.k = el.b[i].b
    else:
      assert(j == 2)
      when RT is SomeFloat:
        result.k = (el.b[i].a + el.b[i].b) * 0.5
      elif RT is SomeInteger:
        result.k = (el.b[i].a + el.b[i].b) div 2
      else:
        assert(false) # do we have a staticAssert() ?
  else:
    assert(false) # do we have a staticAssert() ?

proc tgsCmp[D: Dim; RT, LT](x, y: LTGS[D, RT, LT]; s: int): int =
  tgsCmp[RT, LT](tgsSortKey(x, s), tgsSortKey(y, s))

proc splitOnKey[M, D: Dim; RT, LT](d: seq[LTGS[D, RT, LT]]; s: int; key: TgsSortKey[RT]): (seq[LTGS[D, RT, LT]], seq[LTGS[D, RT, LT]]) =
  # caution, would not work for doublicated keys, so we sort additional by unique id!
  var l = newSeq[LTGS[D, RT, LT]](key.first)
  var h = newSeq[LTGS[D, RT, LT]](d.len - key.first)
  var ll, hh: int
  for el in d:
    if tgsSortKey(el, s) < key:
      l[ll] = el
      inc(ll)
    else:
      h[hh] = el
      inc(hh)
  assert ll == key.first
  assert hh == d.len - key.first
  return (l, h)

proc computeBoundingBoxes[M, D: Dim; RT, LT](d: seq[LTGS[D, RT, LT]]; m: int): (seq[Box[D, RT]], seq[Box[D, RT]]) =
  # Compute the lower and higher bounding boxes of possible binary
  # splits of D list of n rectangles into groups of size m
  assert(m > 0) # the size of each group
  assert(d.len > 0)
  let ng = (d.len + m - 1) div m # `M`, Number of groups
  assert ng == int((d.len.float / m.float).ceil + 0.5)
  var b = newSeq[Box[D, RT]](ng) # list of `M` rectangles
  var l = newSeq[Box[D, RT]](ng - 1) # each a list of M − 1 rectangles
  var h = newSeq[Box[D, RT]](ng - 1)
  for i in 0 ..< ng:
    var s = i * m # + 1
    let t = min(d.high, (i + 1) * m)
    b[i] = d[t].b
    for j in s ..< t:
      b[i] = union(b[i], d[j].b)
    l[0] = b[0]
    h[ng - 2] = b[ng - 1]
  for i in 2 ..< ng: # range as in paper, -1 in []
    l[i - 1] = union(l[i - 2], b[i - 1])
    h[ng - i - 1] = union(b[ng - i], h[ng - i])
  return (l, h)

proc bestBinarySplit[M, D: Dim; RT, LT](d: array[TgsX * D, seq[LTGS[D, RT, LT]]]; m: int): auto =
  # Find the best binary split of D.
  const TgsD = TgsX * D
  assert(m > 0) # the size of each partition.
  let np = (d[0].len + m - 1) div m # `M`, Number of partitions
  assert np == int((d[0].len.float / m.float).ceil + 0.5)
  var cs = RT.high # Inf # Best cost found so far
  var f, b: seq[Box[D, RT]]
  var ss: int # Best sort order
  var key: TgsSortKey[RT]
  for s in 0 ..< TgsD:
    (f, b) = computeBoundingBoxes[M, D, RT, LT](d[s], m)
    for i in 0 .. np - 2:
      let c = area(f[i]) + area(b[i]) # cost(f[i], b[i])
      if c < cs:
        cs = c # Best cost
        ss = s # Best sort order
        key = tgsSortKey(d[s][(i + 1) * m - 0], s) # Sort key of split position # CAUTION, -1
        key.first = (i + 1) * m
  var l, h: array[TgsD, seq[LTGS[D, RT, LT]]]
  for s in 0 ..< TgsD:
    (l[s], h[s]) = splitOnKey[M, D, RT, LT](d[s], ss, key)
  return (l, h)

proc partition[M, D: Dim; RT, LT](d: array[TgsX * D, seq[LTGS[D, RT, LT]]]; m: int): seq[array[TgsX * D, seq[LTGS[D, RT, LT]]]] =
  assert(m > 0)
  if d[0].len <= m: # one partition
    return @[d]
  else:
    let (l, h) = bestBinarySplit[M, D, RT, LT](d, m)
    return partition[M, D, RT, LT](l, m) & partition[M, D, RT, LT](h, m)

proc bulkLoadChunk[M, D: Dim; RT, LT](d: array[TgsX * D, seq[LTGS[D, RT, LT]]]; h: int): (H[M, D, RT, LT], Box[D, RT]) =
  # Bulk load data in D into an R-tree of height h
  for i in d:
    assert i.len > 0
  if h == 0:
    let n = newLeaf[M, D, RT, LT]()
    n.numEntries = d[0].len
    assert(n.numEntries <= M)
    n.level = 0
    var b = d[0][0].b
    for i, el in d[0]: # Note that any of the sorted lists could have been used.
      n.a[i].b = el.b
      n.a[i].l = el.l
      b = union(b, el.b)
    return (n, b)
  else:
    assert(h > 0)
    let n = newNode[M, D, RT, LT]()
    n.level = h
    let m = M ^ h # Desired number of data items under each child of this node.
    let part = partition[M, D, RT, LT](d, m) # Partition of d into k <= M parts.
    assert(part.len <= M)
    for i, p in part:
      (n.a[i].n, n.a[i].b) = bulkLoadChunk[M, D, RT, LT](part[i], h - 1) # Recursively bulk load lower levels of the R-tree.
      n.a[i].n.parent = n
    var b = n.a[0].b
    for i in 1 .. part.high:
      b = union(b, n.a[i].b)
    n.numEntries = part.len
    return (n, b)

template tgsBulkLoadImpl =
  # Top-Down-Greedy-Split bulk loading algorithm
  const TgsD = TgsX * D
  for el in records:
    for d in el.b:
      assert d.a <= d.b
  new result
  result.bigM = M
  var rec = newSeq[LTGS[D, RT, LT]](records.len)
  var d: array[TgsD, seq[LTGS[D, RT, LT]]]
  for i in 0 .. records.high: # we have to create a copy, as we need the ID field for stable sort
    rec[i].b = records[i].b
    rec[i].l = records[i].l
    rec[i].tgsID = i
  for i in 0 ..< TgsD:
    let c = proc (x, y: LTGS[D, RT, LT]): int = tgsCmp(x, y, i) # CAUTION: closure!
    d[i] = sorted(rec, c, SortOrder.Ascending) # Sort d on the ith sort key
  let h = int(ceil(log(records.len.float / M.float, M.float))) # Desired height of the R-tree
  assert h == max(0, int(ceil(log(records.len.float / M.float, M.float)) + 0.5))
  result.root = bulkLoadChunk[M, D, RT, LT](d, h)[0]

proc newRTree*[M, D: Dim; RT, LT](records: seq[L[D, RT, LT]]; minFill: range[30 .. 50] = 40): RTree[M, D, RT, LT] =
  assert(M > 1 and M < 101) # the capacity of leaf- and nonleaf nodes
  tgsBulkLoadImpl
  result.m = max(1, M * minFill div 100)
  assert(0 < result.m and result.m <= M div 2)

proc newRStarTree*[M, D: Dim; RT, LT](records: seq[L[D, RT, LT]]; minFill: range[30 .. 50] = 40): RStarTree[M, D, RT, LT] =
  # NOTE: 2 <= m <= M/2 # page 323
  assert(M > 3 and M < 101)
  tgsBulkLoadImpl
  result.m = max(2, M * minFill div 100)
  assert(1 < result.m and result.m <= M div 2)
  result.p = M * 30 div 100 # for reinsert: remove the first p entries...
  assert(result.p > 0)

# k-nearest neighbor search
# http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.386.8193&rep=rep1&type=pdf

import heapqueue
from math import `^`

type
  QE[M, D: Dim; RT, LT] = ref object of RTRef[RT]
    le: L[D, RT, LT]
    exact: bool

  # unused
  BQE[M, D: Dim; RT, LT] = ref object of RTRef[RT]
    le: L[D, RT, LT]

proc `<`*(a, b: RTRef): bool = a.pri < b.pri

proc dist[D: Dim; RT](qo: BoxCenter[D, RT]; b: Box[D, RT]): RT =
  for i in 0 .. b.high:
    if qo[i] < b[i].a:
      # inc(result, (b[i].a - qo[i]) ^ 2)
      result += (b[i].a - qo[i]) ^ 2
    elif qo[i] > b[i].b:
      # inc(result, (qo[i] - b[i].b) ^ 2)
      result += (qo[i] - b[i].b) ^ 2

# only for testing, returns an not exact result
proc distPlus[D: Dim; RT](qo: BoxCenter[D, RT]; b: Box[D, RT]): RT =
  for i in 0 .. b.high:
    if qo[i] < b[i].a:
      inc(result, (b[i].a - qo[i]) ^ 2)
    elif qo[i] > b[i].b:
      inc(result, (qo[i] - b[i].b) ^ 2)
  return result - 13

proc dist[D: Dim; RT, LT](qo: BoxCenter[D, RT]; l: L[D, RT, LT]): RT =
  for i in 0 .. l.b.high:
    if qo[i] < l.b[i].a:
      # inc(result, (l.b[i].a - qo[i]) ^ 2)
      result += (l.b[i].a - qo[i]) ^ 2
    elif qo[i] > l.b[i].b:
      # inc(result, (qo[i] - l.b[i].b) ^ 2)
      result += (qo[i] - l.b[i].b) ^ 2

# testing proc parameter
proc mydist[D: Dim; RT, LT](qo: BoxCenter[D, RT]; l: L[D, RT, LT]): RT =
  for i in 0 .. l.b.high:
    if qo[i] < l.b[i].a:
      inc(result, (l.b[i].a - qo[i]) ^ 2)
    elif qo[i] > l.b[i].b:
      inc(result, (qo[i] - l.b[i].b) ^ 2)

# http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.386.8193&rep=rep1&type=pdf
# page 276, Fig. 3. Incremental nearest neighbor algorithm.
proc findNearestBox*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; queryObject: BoxCenter[D, RT]): L[D, RT, LT] =
  var queue = initHeapQueue[RTRef[RT]]()
  queue.push(t.root)
  while queue.len > 0:
    var el = queue.pop
    if el of QE[M, D, RT, LT]:
      return QE[M, D, RT, LT](el).le
    elif el of Leaf[M, D, RT, LT]:
      for i, o in Leaf[M, D, RT, LT](el).a:
        if i == Leaf[M, D, RT, LT](el).numEntries: break
        var v = QE[M, D, RT, LT](le: o, pri: dist(queryObject, o.b))
        queue.push(v)
    elif el of Node[M, D, RT, LT]:
      for i, o in (Node[M, D, RT, LT](el).a):
        if i == Node[M, D, RT, LT](el).numEntries: break
        o.n.pri = dist(queryObject, (o).b)
        queue.push(o.n)
    else: assert false

iterator findNearestBox*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; queryObject: BoxCenter[D, RT]): L[D, RT, LT] =
  var queue = initHeapQueue[RTRef[RT]]()
  queue.push(t.root)
  while queue.len > 0:
    var el = queue.pop
    if el of QE[M, D, RT, LT]:
      yield QE[M, D, RT, LT](el).le
    elif el of Leaf[M, D, RT, LT]:
      for i, o in Leaf[M, D, RT, LT](el).a:
        if i == Leaf[M, D, RT, LT](el).numEntries: break
        var v = QE[M, D, RT, LT](le: o, pri: dist(queryObject, o.b))
        queue.push(v)
    elif el of Node[M, D, RT, LT]:
      for i, o in (Node[M, D, RT, LT](el).a):
        if i == Node[M, D, RT, LT](el).numEntries: break
        o.n.pri = dist(queryObject, (o).b)
        queue.push(o.n)
    else: assert false

# Incremental nearest neighbor algorithm for an R-tree where spatial objects are stored "external" to the R-tree.
# This is a function close to the sketch in the paper, using two different data types for object and rectangle.
# Distance for rectangle is an estimation, distance for object is the exact value.
# We do not use this proc, as we do not need two data types, we can just add a field exact: bool to QE.
proc findNearest2[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; queryObject: BoxCenter[D, RT]): L[D, RT, LT] =
  var queue = initHeapQueue[RTRef[RT]]()
  queue.push(t.root)
  while queue.len > 0:
    var el = queue.pop
    if el of QE[M, D, RT, LT] or el of BQE[M, D, RT, LT]:
      if el of BQE[M, D, RT, LT] and queue.len > 0 and dist(queryObject, BQE[M, D, RT, LT](el).le) > queue[0].pri:
        var v = QE[M, D, RT, LT](le: BQE[M, D, RT, LT](el).le, pri: dist(queryObject, BQE[M, D, RT, LT](el).le))
        queue.push(v)
      else:
        return QE[M, D, RT, LT](el).le
    elif el of Leaf[M, D, RT, LT]:
      for i, o in Leaf[M, D, RT, LT](el).a:
        if i == Leaf[M, D, RT, LT](el).numEntries: break
        var v = QE[M, D, RT, LT](le: o, pri: dist(queryObject, o.b))
        queue.push(v)
    elif el of Node[M, D, RT, LT]:
      for i, o in (Node[M, D, RT, LT](el).a):
        if i == Node[M, D, RT, LT](el).numEntries: break
        o.n.pri = dist(queryObject, (o).b)
        queue.push(o.n)
    else: assert false

# Incremental nearest neighbor algorithm for an R-tree where spatial objects are stored "external" to the R-tree.
# Here we use no separate rectangle data type, but use the exact field.
proc findNearest3[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; queryObject: BoxCenter[D, RT]): L[D, RT, LT] =
  var queue = initHeapQueue[RTRef[RT]]()
  queue.push(t.root)
  while queue.len > 0:
    var el = queue.pop
    if el of QE[M, D, RT, LT]:
      if not QE[M, D, RT, LT](el).exact and queue.len > 0 and (var d = dist(queryObject, QE[M, D, RT, LT](el).le); d) > queue[0].pri:
        QE[M, D, RT, LT](el).exact = true
        QE[M, D, RT, LT](el).pri = d
        queue.push(el)
      else:
        return QE[M, D, RT, LT](el).le
    elif el of Leaf[M, D, RT, LT]:
      for i, o in Leaf[M, D, RT, LT](el).a:
        if i == Leaf[M, D, RT, LT](el).numEntries: break
        var v = QE[M, D, RT, LT](le: o, pri: distPlus(queryObject, o.b))
        queue.push(v)
    elif el of Node[M, D, RT, LT]:
      for i, o in (Node[M, D, RT, LT](el).a):
        if i == Node[M, D, RT, LT](el).numEntries: break
        o.n.pri = distPlus(queryObject, (o).b)
        queue.push(o.n)
    else: assert false

# http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.386.8193&rep=rep1&type=pdf
# Incremental nearest neighbor algorithm for an R-tree where spatial objects are stored "external" to the R-tree.
# Fig. 4, page 278
# as proc above, but using proc parameter for exact distance calculation
proc findNearest*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; queryObject: BoxCenter[D, RT]; dst: proc (
    queryObject: BoxCenter[D, RT]; l: L[D, RT, LT]): RT): L[D, RT, LT] =
  var queue = initHeapQueue[RTRef[RT]]()
  queue.push(t.root)
  while queue.len > 0:
    var el = queue.pop
    if el of QE[M, D, RT, LT]:
      if not QE[M, D, RT, LT](el).exact and queue.len > 0 and (var d = dst(queryObject, QE[M, D, RT, LT](el).le); d) > queue[0].pri:
        QE[M, D, RT, LT](el).exact = true
        QE[M, D, RT, LT](el).pri = d
        queue.push(el)
      else:
        return QE[M, D, RT, LT](el).le
    elif el of Leaf[M, D, RT, LT]:
      for i, o in Leaf[M, D, RT, LT](el).a:
        if i == Leaf[M, D, RT, LT](el).numEntries: break
        var v = QE[M, D, RT, LT](le: o, pri: dist(queryObject, o.b))
        queue.push(v)
    elif el of Node[M, D, RT, LT]:
      for i, o in (Node[M, D, RT, LT](el).a):
        if i == Node[M, D, RT, LT](el).numEntries: break
        o.n.pri = dist(queryObject, (o).b)
        queue.push(o.n)
    else: assert false

iterator findNearest*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]; queryObject: BoxCenter[D, RT];
    dst: proc (queryObject: BoxCenter[D, RT]; l: L[D, RT, LT]): RT): L[D, RT, LT] =
  var queue = initHeapQueue[RTRef[RT]]()
  queue.push(t.root)
  while queue.len > 0:
    var el = queue.pop
    if el of QE[M, D, RT, LT]:
      if not QE[M, D, RT, LT](el).exact and queue.len > 0 and (var d = dst(queryObject, QE[M, D, RT, LT](el).le); d) > queue[0].pri:
        QE[M, D, RT, LT](el).exact = true
        QE[M, D, RT, LT](el).pri = d
        queue.push(el)
      else:
        yield QE[M, D, RT, LT](el).le
    elif el of Leaf[M, D, RT, LT]:
      for i, o in Leaf[M, D, RT, LT](el).a:
        if i == Leaf[M, D, RT, LT](el).numEntries: break
        var v = QE[M, D, RT, LT](le: o, pri: dist(queryObject, o.b))
        queue.push(v)
    elif el of Node[M, D, RT, LT]:
      for i, o in (Node[M, D, RT, LT](el).a):
        if i == Node[M, D, RT, LT](el).numEntries: break
        o.n.pri = dist(queryObject, (o).b)
        queue.push(o.n)
    else: assert false

iterator items*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]): L[D, RT, LT] =
  var el: H[M, D, RT, LT] = t.root
  assert el.parent == nil
  el.cur = 0
  while el != nil:
    if el of Leaf[M, D, RT, LT]:
      for i, o in Leaf[M, D, RT, LT](el).a:
        if i == Leaf[M, D, RT, LT](el).numEntries: break
        yield o
      el = el.parent
    elif el of Node[M, D, RT, LT]:
      if el.cur < el.numEntries:
        let h = el
        el = Node[M, D, RT, LT](el).a[el.cur].n
        assert el.parent == h
        el.cur = 0
        h.cur += 1
      else:
        el = el.parent
    else: assert false

iterator elements*[M, D: Dim; RT, LT](t: RTree[M, D, RT, LT]): LT =
  var el: H[M, D, RT, LT] = t.root
  assert el.parent == nil
  el.cur = 0
  while el != nil:
    if el of Leaf[M, D, RT, LT]:
      for i, o in Leaf[M, D, RT, LT](el).a:
        if i == Leaf[M, D, RT, LT](el).numEntries: break
        yield o.l
      el = el.parent
    elif el of Node[M, D, RT, LT]:
      if el.cur < el.numEntries:
        let h = el
        el = Node[M, D, RT, LT](el).a[el.cur].n
        assert el.parent == h
        el.cur = 0
        h.cur += 1
      else:
        el = el.parent
    else: assert false

# testing findNearest() with a custom object, instead plain rectangle
when isMainModule:

  type
    Circ = object
      x, y, r: float

  # squared distance from query point to circle
  proc dst(qo: BoxCenter[2, float]; l: L[2, float, Circ]): float =
    let c = l.l
    max(0, math.sqrt((qo[0] - c.x) ^ 2 + (qo[1] - c.y) ^ 2) - c.r) ^ 2

  # bounding box of circle
  proc box(c: Circ): Box[2, float] =
    result[0].a = c.x - c.r
    result[0].b = c.x + c.r
    result[1].a = c.y - c.r
    result[1].b = c.y + c.r

  # the stupid test-all proc to veryfy our RTree results
  proc nearest_seq(s: seq[Circ]; qo: array[2, float]): Circ =
    var min = Inf
    for c in s:
      if (var m = max(0, math.sqrt((qo[0] - c.x) ^ 2 + (qo[1] - c.y) ^ 2) - c.r); m) < min:
        min = m
        result = c

  import random
  proc fullTest =
    echo "full nearest test"
    var t = newRStarTree[4, 2, float, Circ]()
    var s: seq[Circ]
    for i in 0 .. 1000:
      let a = Circ(x: rand(1000).float, y: rand(1000).float, r: rand(12).float)
      s.add(a)
      var el: L[2, float, Circ]
      el = (box(a), a)
      t.insert(el)
    for i in 0 .. 199:
      let qo = [rand(1200).float, rand(1200).float]
      let e1 = t.findNearest(qo, dst)[1]
      var e0: type(e1)
      # test the iterator -- well we test only the first result here
      for el in t.findNearest(BoxCenter[2, float](qo), dst): # why do we here need BoxCenter[2, float]() but not 2 lines above?
        e0 = el.l
        break
      let e2 = nearest_seq(s, qo)
      assert(e1.x == e0.x and e1.y == e0.y and e1.r == e0.r)
      assert e1 == e0 # well we can compare the objects -- but caution, for ref object addr is compared by default, not content
      if not (e1.x == e2.x and e1.y == e2.y and e1.r == e2.r): # circs may differ, but at least dist should match
        let d1 = max(0, math.sqrt((qo[0] - e1.x) ^ 2 + (qo[1] - e1.y) ^ 2) - e1.r)
        let d2 = max(0, math.sqrt((qo[0] - e2.x) ^ 2 + (qo[1] - e2.y) ^ 2) - e2.r)
        echo e1, d1
        echo e2, d2
        assert d1 == d2 # shoud match exactly, no eps math needed?
  #
  fullTest()

  # a simple test
  proc circTest =
    var t = newRStarTree[4, 2, float, Circ](50)
    let a = Circ(x: 10, y: 3, r: 2)
    var el: L[2, float, Circ]
    el = (box(a), a)
    t.insert(el)
    let b = Circ(x: -10, y: 3, r: 3)
    t.insert(L[2, float, Circ]((box(b), b)))
    let c = Circ(x: 2, y: 9, r: 1)
    t.insert(L[2, float, Circ]((box(c), c)))
    echo "nearest: ", t.findNearest([-2.0, 1], dst)
    assert t.findNearest([-2.0, 1], dst).l == b
    assert t.findNearest([7.0, 1], dst) == el
    #quit()
  #
  circTest()

# testing all the other procs -- but only for rectangle in 2D
when isMainModule:

  # we can launch a plain GUI to visualize the rectangle orderings
  when defined(cairoGTK):
    import gintro/cairo
    import drawingarea
    from math import PI

    proc extents(): (float, float, float, float) =
      (-0.100, -0.100, 1200.0, 1200.0) # ugly float literals

    # draw to cairo context

    proc tgsDebug[M, D: Dim; RT, LT](n: H[M, D, RT, LT]) =
      proc draw(cr: cairo.Context) =
        cr.setSource(1, 1, 1) # set background color and paint
        cr.paint
        cr.setSource(0, 0, 0) # forground color
        proc tDebug[M, D: Dim; RT, LT](n: H[M, D, RT, LT]; cr: cairo.Context) =
          if n of Leaf[M, D, RT, LT]:
            cr.setSource(0, 0, 1, 0.3)
            for i in 0 ..< n.numEntries:
              let b = Leaf[M, D, RT, LT](n).a[i].b
              let (x, y) = (b[0].a, b[1].a)
              let (w, h) = (b[0].b - x, b[1].b - y)
              cr.rectangle(x.float, y.float, w.float, h.float)
            cr.stroke
          elif n of Node[M, D, RT, LT]:
            for i in 0 ..< n.numEntries:
              let b = Node[M, D, RT, LT](n).a[i].b
              let (x, y) = (b[0].a, b[1].a)
              let (w, h) = (b[0].b - x, b[1].b - y)
              let paint = min(0.3 + n.level.float * 0.3, 1)
              cr.setSource(0, 0, 0, paint)
              cr.rectangle(x.float, y.float, w.float, h.float)
              cr.stroke
              tDebug(Node[M, D, RT, LT](n).a[i].n, cr)
        #
        tDebug[M, D, RT, LT](n, cr)

      var data: PDA_Data
      data.draw = draw
      data.extents = extents
      data.windowSize = (800, 600)
      newDisplay(data)
    #
    proc tgsDebug[M, D: Dim; RT, LT](t: RStarTree[M, D, RT, LT]) =
      tgsDebug(t.root)

  # test our sortPlus() proc
  var t = [4, 1, 3, 2]
  var xt = 7
  sortPlus(t, xt, system.cmp, SortOrder.Ascending)
  assert(xt == 1 and t == [2, 3, 4, 7])

  type
    RSE = L[2, int, int]
    RSeq = seq[RSE]

  # the stupid resq_ procs to verify our RTree results
  proc rseq_search(rs: RSeq; rse: RSE): RSeq = #seq[int] =
    for i in rs:
      if intersect(i.b, rse.b):
        result.add(i)

  proc rseq_nearest[D, RT](rs: RSeq; n: BoxCenter[D, RT]): auto =
    assert rs.len > 0
    result = rs[0]
    var min = int.high
    for el in rs:
      let m = dist(n, el.b)
      if m < min:
        min = m
        result = el

  proc rseq_delete(rs: var RSeq; rse: RSE): bool =
    for i in 0 .. rs.high:
      if rs[i] == rse:
        #rs.delete(i)
        rs[i] = rs[rs.high]
        rs.setLen(rs.len - 1)
        return true

  import random, algorithm, times

  # a basic nearest neighbour test
  proc fnntest =
    var t = newRStarTree[4, 2, int, int]()
    var el: L[2, int, int]
    el = ( [(5, 6), (7, 8)], 0)
    t.insert(el)
    el = ( [(2, 5), (3, 7)], 0)
    t.insert(el)
    el = ( [(8, 8), (9, 11)], 0)
    t.insert(el)
    let xb: BoxCenter[2, int] = [0, 0]
    echo "nearest: ", t.findNearestBox(xb)
    echo "nearest: ", t.findNearest2(xb)

  # testing interleaved insert, delete, search...

  proc nextId(): int =
    var i {.global.}: int
    inc(i)
    return i

  proc `<`(a, b: L[2, int, int]): bool =
    a.l < b.l # plain sort by id

  proc ignore(a, b: seq[RSE]): bool =
    if a.len != b.len: return false
    for i in 0 .. a.high:
      if a[i].l != b[i].l or a[i].b != b[i].b:
        return false
    return true

  proc test(n: int) =
    var b: Box[2, int]
    echo center(b)
    var x1, x2, y1, y2: int
    var t = newRStarTree[4, 2, int, int]()
    ### var t = newRTree[5, 2, int, int]() # let's test basic RTree with odd entries too!
    var ttgs: RStarTree[4, 2, int, int]
    ### var ttgs: RTree[13, 2, int, int] # let's test basic RTree with odd entries too!
    var rs: seq[RSE]
    for i in 0 .. 5:
      for i in 0 .. n - 1:
        x1 = rand(1000)
        y1 = rand(1000)
        x2 = x1 + rand(25)
        y2 = y1 + rand(25)
        b = [(x1, x2), (y1, y2)]
        let el: L[2, int, int] = (b, nextID()) # unique id, so that we can stable sort and compare
        t.insert(el)
        rs.add(el)

      let st = getTime()
      ttgs = newRStarTree[4, 2, int, int](rs, 40)
      ### ttgs = newRTree[13, 2, int, int](rs, 40)
      echo "TGS Bulk load ", rs.len, " elements in: ", (getTime() - st)

      let xb: BoxCenter[2, int] = [1, 2]
      echo "nearest: ", t.findNearestBox(xb)

      for i in 0 .. (n div 4):
        let j = rand(rs.high)
        var el = rs[j]
        assert t.delete(el)
        assert ttgs.delete(el)
        assert rs.rseq_delete(el)

      for i in 0 .. n - 1:
        x1 = rand(1000)
        y1 = rand(1000)
        x2 = x1 + rand(100)
        y2 = y1 + rand(100)
        b = [(x1, x2), (y1, y2)]
        let el: L[2, int, int] = (b, i)
        let r = search(t, b)
        let r3 = search(ttgs, b)
        let r2 = rseq_search(rs, el)
        assert r.len == r2.len
        assert r.sorted() == r2.sorted()
        assert r3.len == r2.len
        assert r3.sorted(system.cmp) == r2.sorted(system.cmp)
        let c = center(b)
        let aaa = rseq_nearest(rs, c).b
        let bbb = t.findNearestBox(c).b
        var fff: type(bbb)
        for el in t.findNearestBox(c):
          fff = el.b
          break
        let ccc = t.findNearest2(c).b
        let ddd = t.findNearest3(c).b
        let eee = t.findNearest(c, mydist[2, int, int]).b
        let dst = dist(c, aaa)
        if dst != dist(c, bbb) or dst != dist(c, ccc) or dst != dist(c, ddd) or dst != dist(c, eee) or dst != dist(c, fff):
          echo dst, dist(c, bbb), dist(c, ccc), dist(c, ddd), dist(c, eee), dist(c, fff)
          assert false

    rs.setLen(112) # to give us an interesting but not overpopulated picture

    echo "tgsBulkLoad: ", rs.len
    var tgs = newRStarTree[4, 2, int, int](rs, 40)
    when defined(cairoGTK):
      tgsDebug(tgs)

  test(550) # should be enough for testing, but feel free to increase...
  # test(5500)
  fnntest()

  # 1305 lines

