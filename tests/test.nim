import rtree
from math import sqrt, `^`

type
  Circ = object
    x, y, r: float

# squared distance from query point to circle
proc dist(qo: BoxCenter[2, float]; l: L[2, float, Circ]): float =
  let c = l.l
  max(0, math.sqrt((qo[0] - c.x) ^ 2 + (qo[1] - c.y) ^ 2) - c.r) ^ 2

# bounding box of circle
proc box(c: Circ): Box[2, float] =
  result[0].a = c.x - c.r
  result[0].b = c.x + c.r
  result[1].a = c.y - c.r
  result[1].b = c.y + c.r

proc test =
  const P = [(9, 3, 2), (-2, 2, 1), (-5, -3, 2), (4, -2, 1)]
  var s: seq[L[2, float, Circ]] # buffer for bulk load
  var t = newRStarTree[8, 2, float, Circ]()
  var el: L[2, float, Circ]
  for p in P:
    let c = Circ(x: p[0].float, y: p[1].float, r: p[2].float)
    el = (box(c), c)
    s.add(el)
    t.insert(el)
  echo "circ in first quadrant:"
  echo t.search([(0.0, 12.0), (0.0, 12.0)])
  echo "circs below x axis"
  echo t.search([(-20.0, 20.0), (-12.0, 0.0)])
  echo "empty area"
  echo t.search([(0.0, 5.0), (0.0, 5.0)])

  echo "search a single circle loacated closest to origin using only bounding boxes"
  echo t.findNearestBox(BoxCenter[2, float]([0.0, 0.0]))
  echo "query circles sorted along x-axis, using only bounding boxes"
  for el in t.findNearestBox(BoxCenter[2, float]([-100.0, 0.0])): # sort along x axis
    echo el.l

  echo "search a single circle located closest to origin using exact dist() function"
  echo t.findNearest(BoxCenter[2, float]([0.0, 0.0]), dist)
  echo "query circles sorted along x-axis, using dist() function"
  for el in t.findNearest(BoxCenter[2, float]([-100.0, 0.0]), dist):
    echo el.l

  # and we can delete objects:
  assert(t.delete(s[0]))
  assert(not t.delete(s[0])) # that object was already deleted

  var bt = newRStarTree[8, 2, float, Circ](s) # a bulk loaded R-Tree, should work like t
  echo "done!"

test()


