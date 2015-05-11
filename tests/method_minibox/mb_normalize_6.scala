package miniboxing.tests.correctness


object SpCls6Obj {
  def normalized[@specialized U, @specialized V](u: U, v: V) = ???
}

class SpCls6[@specialized S] {
  def normalizeMe[@specialized T](s: S, t: T) = SpCls6Obj.normalized(s, t)
}
