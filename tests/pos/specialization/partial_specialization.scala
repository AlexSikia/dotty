object partial_specialization {
  def foo[T, @specialized(Int, Float) U](a: T, b: U): U = b
  def bar[@specialized(Int, Float) T, @specialized(Int, Float) U](a: T, b: U): U = b
}