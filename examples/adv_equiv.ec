cnst q : int.

adversary A(x:int) : int {int -> int}.

game G1 = {
  var dumb : int

  fun five(y:int) : int = {
    return 5;
  }

  abs A = A{five}

  fun Main() : bool = {
    var tmp : int;
    dumb = 2;
    tmp = A(1);
    return (tmp=5);
  }
}.

game G2 = G1
where Main = {
    var tmp : int;
    dumb = 1;
    tmp = A(1);
    return (tmp=5);
  }.


equiv G1_A_G2_A : G1.A ~ G2.A: ={x,dumb} ==> ={res} by auto.

(* Conclusion: adversary has access to all of the global variables. *)

equiv G1_A_G2_A_2 : G1.A ~ G2.A: ={x} ==> ={res} by auto.