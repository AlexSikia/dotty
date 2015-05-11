package miniboxing.tests.correctness


class SpCls2[@specialized S] {
  def normalizeMe[@specialized T](s: S, t: T): T = t
}
