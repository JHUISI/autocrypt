(* prover alt-ergo, cvc3. *)

type group.

adversary A() : int {}.

game simple = {

  abs A  = A {}

  fun Main() : bool = {
    var x : int;
    var y : int;


    y=4;
    x = A();
    return (x=5);
  }

  fun new() : bool = {
    return true;
  }
}.


game simple2 = simple


  where Main = {
  var x : int;
  var y : int;

  y=5;
  x=A();
  return (x=5);
}.


(* equiv A_and_A : simple.A ~ simple2.A: true ==> ={res}. *)


equiv simple1_2 : simple.Main ~ simple2.Main: true ==> ={res}.
call.
trivial.
save.

game testcall = simple
where new = {
  var b: bool;

  b=Main();
  return b;
}.

game testcall2 = simple2
where new = {
  var b: bool;
  var z: int;

  z=6;

  b=Main();
  return b;
}. 

equiv tmain1_2 : testcall.Main ~ testcall2.Main: true ==> ={res}.
call.
trivial. 
save.


equiv new1_2 : testcall.new ~ testcall2.new: true ==> ={res}.
call using tmain1_2.
trivial.

