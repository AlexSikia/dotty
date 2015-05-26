object multi_specialization {
  //def one[@specialized T](n: T): T = n
  def two[@specialized(Double) T, U](n: T, m: U): (T,U) = (n,m)
  def three[@specialized(Long) T, U,@specialized(Int) V](n: T, m: U, o: V): (T,U,V) = (n,m,o)
}