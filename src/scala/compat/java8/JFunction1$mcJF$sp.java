
/*
 * Copyright (C) 2012-2014 Typesafe Inc. <http://www.typesafe.com>
 */

package scala.compat.java8;

@FunctionalInterface
public interface JFunction1$mcJF$sp extends JFunction1 {
    abstract long apply$mcJF$sp(float v1);

    default Object apply(Object t) { return (Long) apply$mcJF$sp((Float) t); }
}
