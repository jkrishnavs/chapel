class Foo {
  var s: sync int;
}

var foo1 = new Foo();
writeln(foo1.s.isFull);
delete foo1;
