class Foo[@specialized +A] {
  def bop[@specialized B >: A] = new Bar[B](this)
}

class Bar[@specialized a](f: Foo[a])