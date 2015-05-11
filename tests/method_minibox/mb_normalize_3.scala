package miniboxing.tests.correctness


class SpCls3[@specialized S] {
  def normalizeMe[@specialized T](s: S, t: T): SpCls3[T] = new SpCls3[T]
}
