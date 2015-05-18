sealed abstract class Foo[@specialized +A] {
  def bop[@specialized B >: A]: Foo[B] = new Bar[B](this)
}

case class Bar[@specialized a](tl: Foo[a]) extends Foo[a]