package miniboxing.tests.compile.tparams



class TParams1[@specialized T] {
  def foo[X](t: T, x: X) = 12
}
