class Foo[@specialized +A] {
  def bop[@specialized B >: A] = new Bar[B](this)
  //def x[x](x:x)=x
}

class Bar[@specialized a](f: Foo[a])