prover alt-ergo, z3, cvc3.

timeout 10.

game G1 = {
  var glob : int
  var nums : int list

  fun foo(b : bool) : int = {
    var r : int;
    r = [0..5];
    return r;
  }

  fun main() : bool = {
    var eq : bool;
    var choose : bool;
    var foo_ret : int;
    glob = [0..5];

    choose = {0,1};

    foo_ret = foo(choose);
    eq = (foo_ret = 2);
    return eq;
  }
}.

game G2 = G1 
  where foo = {
    var r : int;
    r = [0..5];
    if(b) {
      r = glob;
    }
    return r;
  }
.
