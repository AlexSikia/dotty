
/*
 * Copyright (C) 2012-2014 Typesafe Inc. <http://www.typesafe.com>
 */

package scala.compat.java8;

@FunctionalInterface
public interface JFunction2$mcJDJ$sp extends JFunction2 {
    abstract long apply$mcJDJ$sp(double v1, long v2);

    default Object apply(Object v1, Object v2) { return (Long) apply$mcJDJ$sp((Double) v1, (Long) v2); }
}
