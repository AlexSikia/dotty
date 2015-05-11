package miniboxing.tests.correctness


object SpCls7Obj {
  def normalized[@specialized U, @specialized V](u: U, v: V): U = ???
}

class SpCls7[@specialized S] {
  def normalizeMe[@specialized T](s: S, t: T): S = SpCls7Obj.normalized(s, t)
}
