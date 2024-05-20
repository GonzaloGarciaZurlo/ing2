// // https://dafny.org/dafny/OnlineTutorial/guide

// method Abs(x: int) returns (y: int)
//   ensures 0 <= y
//   ensures 0 <= x ==> y == x // esto resuelve el problema del assert de testing pero no esta bien! Tambien se cuemple para negativos por la pre falsa
//   ensures x < 0 ==> y == -x //esto resuelve el problema de arriba y "define" de alguna manera el metodo Abs
// {
//   if x < 0 {
//     return -x;
//   } else {
//     return x;
//   }
// }

// method MultipleReturns(x: int, y: int) returns (more: int, less: int)
//   ensures less < x
//   ensures x < more
// {
//   more := x + y;
//   less := x - y;
// }

// method MultipleReturns'(x: int, y: int) returns (more: int, less: int)
//   ensures less < x < more
// {
//   more := x + y;
//   less := x - y;
// }

// method MultipleReturns''(x: int, y: int) returns (more: int, less: int)
//   requires 0 < y
//   ensures less < x < more
// {
//   more := x + y;
//   less := x - y;
// }

// method Max(a: int, b: int) returns (c: int)
//   // What postcondition should go here, so that the function operates as expected?
//   // Hint: there are many ways to write this.
//   ensures c >= a && c >= b
// {
//   // fill in the code here
//   if (a < b) {
//     return b;
//   }
//   return a;
// }

// method Testing()
// {
//   assert 2 < 3;
//   // Try "asserting" something that is not true.
//   // What does Dafny output?
// }

// method Testing'() {
//   // Assert some things about Max. Does it operate as you expect?
//   // If it does not, can you think of a way to fix it?
//   var m := Max(5,-5);
//   assert m >= 5;
//   //can't do assert m == 5;
// }


// method Testing''()
// {
//   var v := Abs(3);
//   assert 0 <= v;
//   assert v == 3;
// }

// method Abs'(x: int) returns (y: int)
//   // Add a precondition here so that the method verifies.
//   requires x == -1
//   // Don't change the postconditions.
//   ensures 0 <= y
//   ensures 0 <= x ==> y == x
//   ensures x < 0 ==> y == -x
// {
//   y:= x + 2;
// }

// method Abs2(x: int) returns (y: int)
//   // Add a precondition here so that the method verifies.
//   // Don't change the postconditions.
//   ensures 0 <= y
//   ensures 0 <= x ==> y == x
//   ensures x < 0 ==> y == -x
// {
//   y:= x + 1;
// }

// // functions only have one expresion

// function abs(x: int): int
// {
//   if x < 0 then -x else x
// }

// method m()
// {
//     assert abs(3) == 3;
// }

// function max(a: int, b: int): int
// {
//     if a > b then a else b
// }

// method Testing'''(){
//     var m := max(5,-5);
//     assert m == 5;
// }

// method UltiamteAbs(x: int) returns (y: int)
//   // Use abs here, then confirm the method still verifies.
//   ensures y == abs(x)
// {
//   // Then change this body to also use abs.
//   if x < 0 {
//     return -x;
//   } else {
//     return x;
//   }
// }


function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib'(n: nat) returns (b: nat)
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

method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  var i: int := 0;
  var a := 1;
  b := 0;
  while i < n
    invariant 0 <= i <= n
    invariant i == 0 ==> a == 1
    invariant i > 0 ==> a == fib(i-1)
    invariant b == fib(i)
  {
    a, b := b, a + b;
    i := i + 1;
  }
}

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    if a[index] == key { return; }
    index := index + 1;
  }
  index := -1;
}



method FindMax(a: array<int>) returns (i: int)
  requires a.Length >= 1
  ensures 0 <= i < a.Length && forall k :: 0 <= k < a.Length ==> a[i] >= a[k]
  // Annotate this method with pre- and postconditions
  // that ensure it behaves as described.
{
  // Fill in the body that calculates the INDEX of the maximum.
  i := 0;
  var k:= 1;
  while k < a.Length
    invariant 0 <= i < a.Length
    invariant forall j :: 0 <= j < k ==> j < a.Length && a[i] >= a[j]
{
    if a[k] > a[i]
    {
      i := k;
    }
    k := k + 1;
  }
}

predicate sorted(a: array?<int>)
  reads a
{
  a != null ==> forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i ::
      0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value {
      low := mid + 1;
    } else if value < a[mid] {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
}
