package miniboxing.tests.compile


class Norm1 {
  def overrideMe[@specialized A, @specialized B, @specialized C](a: A, b: B, c: C): A = a
}

class Norm2 extends Norm1 {
  override def overrideMe[@specialized A, B, @specialized C](a: A, b: B, c: C): A = ???
}
