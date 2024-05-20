function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  var i := 0;
  var c := 1;
  b := 0;
  while i < n
    invariant 0 <= i <= n
    invariant c == fib(i + 1)
    invariant b == fib(i)
  {
    b, c := c, c + b;
    i := i + 1;
  }
}

method Main() {
    var n := 5;
    var fibo := ComputeFib(n);
    print "Fibonachi of ";
    print n;
    print " is ";
    print fibo;
    print "\n";
}

