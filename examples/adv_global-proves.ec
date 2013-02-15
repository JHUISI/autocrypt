(** Abstract Types **)
type group.
type message.
type key_pair.
type secret_key. 
type public_key.

cnst g:group.
cnst bad_h:group.

(** Abstract procedures **)
adversary A() : message * group {message -> group}.

(** Game definitions **)

(*
** Game EF:
**
** This is the standard existential forgery experiment for FDH
*)
game G1 = {
  var L : (message, group) map
  var S : message list
  var i : int
  var M : (int, message) map
  var I : (message, int) map
  var mm : message
  var sigma : group
    
  fun H(m:message) : group = {
      I[m] = i; (* the reverse map *)
    return g;
  }

  abs A = A {H}
  
  fun Main() : bool = {
    var h : group;
    S = [];
    i = 0;
    (mm, sigma) = A();
    h = H(mm);
    return (h = bad_h);
  }
}.

game G2 = G1 

 where H = {
  return g;
 }. 

(* want to come back to this *)
(*
equiv G1_A_G2_A : G1.A ~ G2.A: ((i{2} <= j{2} || in_dom(M{2}[j{2}], L{2})) && ={sigma,mm,j,M,i,sk,pk,S,L}) ==> ={res} by auto.
*)

equiv G1_G2 : G1.Main ~ G2.Main:
 true ==> ={res}.
inline H.
derandomize.
wp.
call (={S,i}).
auto.

