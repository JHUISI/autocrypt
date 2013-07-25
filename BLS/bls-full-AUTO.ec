prover alt-ergo, z3, cvc3.

type G_1.
type G_T.
type message.

cnst g_1_i : G_1.
cnst g_T_i : G_T.
cnst g : G_1.
cnst q : int.
cnst queries : int.

op [*] : (G_1, G_1) -> G_1 as G_1_mul.
op [^] : (G_1, int) -> G_1 as G_1_pow.

op [*] : (G_T, G_T) -> G_T as G_T_mul.
op [^] : (G_T, int) -> G_T as G_T_pow.

op G_1_log : G_1 -> int.
op G_T_log : G_T -> int.

op e : (G_1, G_1) -> G_T as G_1_pair.

(* 
   From easycrypt ElGamal:
   If we use the native modulo alt-ergo is not able
   to perform the proof.
   So we declare an operator (%%) which stand for the modulo ...
*)

op [%%] : (int,int) -> int as int_mod.

axiom q_pos : 0 < q.

(* Axioms largely pulled from ElGamal.  Note that G_1 and G_T have the same order if the order is prime. *)

axiom G_1_mult_1 : forall (x : G_1), x * g_1_i = x.
axiom G_1_exp_0 : forall (x : G_1), x ^ 0 = g_1_i.
axiom G_1_exp_S : forall (x : G_1, k : int), k > 0 => x ^ k = x * (x^(k-1)).

axiom G_T_mult_1 : forall (x : G_T), x * g_T_i = x.
axiom G_T_exp_0 : forall (x : G_T), x ^ 0 = g_T_i.
axiom G_T_exp_S : forall (x : G_T, k : int), k > 0 => x ^ k = x * (x^(k-1)).

axiom bilinearity : forall (x : G_1, y : G_1, a : int, b : int), e(x ^ a, y ^ b) = e(x, y) ^ (a * b).
(* axiom non_degenerate : !(e(g_1_i, g_1_i) = g_T_i). *)

axiom G_1_pow_add : 
 forall (x, y:int), g_1_i ^ (x + y) = g_1_i ^ x * g_1_i ^ y.

axiom G_T_pow_add : 
 forall (x, y:int), g_T_i ^ (x + y) = g_T_i ^ x * g_T_i ^ y.

axiom G_1_pow_mult :
 forall (x, y:int),  (g_1_i ^ x) ^ y = g_1_i ^ (x * y).

axiom G_T_pow_mult :
 forall (x, y:int),  (g_T_i ^ x) ^ y = g_T_i ^ (x * y).

axiom G_1_log_pow : 
 forall (g_1_i':G_1), g_1_i ^ G_1_log(g_1_i') = g_1_i'.

axiom G_T_log_pow : 
 forall (g_T_i':G_T), g_T_i ^ G_T_log(g_T_i') = g_T_i'.

axiom G_1_pow_mod : 
 forall (z:int), g_1_i ^ (z%%q) = g_1_i ^ z.

axiom G_T_pow_mod : 
 forall (z:int), g_T_i ^ (z%%q) = g_T_i ^ z.


axiom mod_add : 
 forall (x,y:int), (x%%q + y)%%q = (x + y)%%q.

axiom mod_small : 
 forall (x:int), 0 <= x => x < q => x%%q = x.

axiom mod_sub : 
 forall (x, y:int), (x%%q - y)%%q = (x - y)%%q. 

axiom mod_bound : 
 forall (x:int), 0 <= x%%q && x%%q < q. 


pop KG   : () -> (int).
pop Rand_G_1 : () -> (G_1).

axiom Rand_G_1_def() : x = Rand_G_1() ~ y = [0..q] : true ==> x = g_1_i ^ y.

adversary Adv (adv_public_key : G_1) : (message * G_1) {message -> G_1

game blsfull_EF = {
  var sk : Z_R
  var pk : G_1
  var queried : message list
  var rand_oracle : (message, G_1) map

  fun Hash(m : message) : G_1 = {
    if(!in_dom(m, rand_oracle)) {
      rand_oracle[m] = Rand_G_1();
    }
    return rand_oracle[m];
  }

  fun Sign(m : message) : G_1 = {
    var sig2 : G_1;
    var sig : G_1;
    var output : G_1;
    sig = (Hash(M) ^ sk);
    sig2 = Hash(M);
    output = sig;
    queried = m :: queried;
    return output;
  }

  abs A = Adv{Hash, Sign}

  fun Verify(pk : G_1, m : message, sig : G_1, g : G_1) : bool = {
    var output : bool;
    var h : G_1;
    h = Hash(M);
    output = (e(h, pk) = e(sig, g));
    return output;
  }

  fun Init() : bool = {
    var x : Z_R;
    var g : G_1;
    g = Rand_G_1();
    x = Rand_Z_R();
    pk = (g ^ x);
    sk = x;
    rand_oracle = empty_map;
    queried = [];
    return true;
  }

  fun Main() : bool = {
    var m : message;
    var sig : G_1;
    var g : G_1;
