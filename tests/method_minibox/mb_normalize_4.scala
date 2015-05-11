package miniboxing.tests.correctness


class SpCls4Tuple2[@specialized U, @specialized V](val u: U, val v: V)

class SpCls4[@specialized S] {
  def normalizeMe1[@specialized T](s: S, t: T) = new SpCls4Tuple2(s, t)
}
