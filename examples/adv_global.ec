cnst dummy:int.

adversary A() : int {int -> int}.

game G1 = {
  var diff : int
    
  fun f(x:int) : int = {
    diff = 5;  (* can also comment this out *)
    return dummy;
  }

  abs A = A{f}
  
  fun Main() : int = {
    var aRet:int;
    diff = 2;  (* can also comment this out *)
    aRet=A();
    return aRet;
  }
}.

game G2 = G1 
 where f = {
  return dummy;
 }. 

(* unnecessary, but here to be very clear *)
equiv G1_f_G2_f : G1.f ~ G2.f : true ==> ={res}.
trivial.
save.

(* also unnecessary and implied by the above, but here to be very clear *)
equiv G1_f_G2_f2 : G1.f ~ G2.f : ={x} ==> ={res}.
trivial.
save.

(* output produced by the call below *)
equiv inferred_G1_A_G2_A_5 : G1.A ~ G2.A : true ==> ={res} by auto.


equiv G1_G2 : G1.Main ~ G2.Main:
 true ==> ={res}.
call (true).
auto.



(* email list *)

(* want to come back to this *)
(*
equiv G1_A_G2_A : G1.A ~ G2.A: ((i{2} <= j{2} || in_dom(M{2}[j{2}], L{2})) && ={sigma,mm,j,M,i,sk,pk,S,L}) ==> ={res} by auto.
*)
