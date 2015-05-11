package miniboxing.tests.correctness


object Obj {
  def normalizeMe1[@specialized T](t: T): T = t
}

class Cls {
  def normalizeMe2[@specialized T](t: T): T = t
}

class SpCls[@specialized S] {
  def normalizeMe3[@specialized T](t: T): T = t
}
