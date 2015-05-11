package miniboxing.tests.correctness


class Sp5Tuple2[@specialized U, @specialized V](u: U, v: V)

object Sp5Test {
  def normalize[@specialized S, @specialized T](s: S, t: T) = {
    def foo = {
      def bar = {
        new Sp5Tuple2(s, t)
      }
      bar
    }
    foo
  }
}
