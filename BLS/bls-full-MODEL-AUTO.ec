prover alt-ergo, z3, cvc3.

type G_1.
type G_2.
type G_T.
type message.

cnst g_1_i : G_1.
cnst g_2_i : G_2.
cnst g_T_i : G_T.
cnst g_1 : G_2.
cnst g_2 : G_1.
cnst g_T : G_T.
cnst q_1 : int.
cnst q_2 : int.
cnst q_T : int.

cnst q : int.

cnst limit_Hash : int.

op [*] : (G_1, G_1) -> G_1 as G_1_mul.
op [*] : (G_2, G_2) -> G_2 as G_2_mul.
op [^] : (G_1, int) -> G_1 as G_1_pow.
op [^] : (G_2, int) -> G_2 as G_2_pow.

op [*] : (G_T, G_T) -> G_T as G_T_mul.
op [^] : (G_T, int) -> G_T as G_T_pow.

op G_1_log : G_1 -> int.
op G_2_log : G_2 -> int.
op G_T_log : G_T -> int.

op e : (G_1, G_2) -> G_T as G_1_G_2_pair.

(*
   From easycrypt ElGamal:
   If we use the native modulo alt-ergo is not able
   to perform the proof.
   So we declare an operator (%%) which stand for the modulo ...
*)

op [%%] : (int,int) -> int as int_mod.

axiom q_1_pos : 0 < q_1.
axiom q_2_pos : 0 < q_2.
axiom q_T_pos : 0 < q_T.

axiom q_pos : 0 < q.

(* Axioms largely pulled from ElGamal.  Note that G_1, G_2, and G_T have the same order if the order is prime. *)

axiom G_1_mult_1 : forall (x : G_1), x * g_1_i = x.
axiom G_1_exp_0 : forall (x : G_1), x ^ 0 = g_1_i.
axiom G_1_exp_S : forall (x : G_1, k : int), k > 0 => x ^ k = x * (x^(k-1)).

axiom G_2_mult_1 : forall (x : G_2), x * g_2_i = x.
axiom G_2_exp_0 : forall (x : G_2), x ^ 0 = g_2_i.
axiom G_2_exp_S : forall (x : G_2, k : int), k > 0 => x ^ k = x * (x^(k-1)).

axiom G_T_mult_1 : forall (x : G_T), x * g_T_i = x.
axiom G_T_exp_0 : forall (x : G_T), x ^ 0 = g_T_i.
axiom G_T_exp_S : forall (x : G_T, k : int), k > 0 => x ^ k = x * (x^(k-1)).

axiom bilinearity : forall (x : G_1, y : G_2, a : int, b : int), e(x ^ a, y ^ b) = e(x, y) ^ (a * b).
(* axiom non_degenerate : !(e(g_1, g_2) = g_T_i). *)

axiom G_2_pow_add_1 :
 forall (x, y:int), g_1 ^ (x + y) = g_1 ^ x * g_1 ^ y.

axiom G_1_pow_add_2 :
 forall (x, y:int), g_2 ^ (x + y) = g_2 ^ x * g_2 ^ y.

axiom G_T_pow_add :
 forall (x, y:int), g_T ^ (x + y) = g_T ^ x * g_T ^ y.

axiom G_2_pow_mult_1 :
 forall (x, y:int),  (g_1 ^ x) ^ y = g_1 ^ (x * y).

axiom G_1_pow_mult_2 :
 forall (x, y:int),  (g_2 ^ x) ^ y = g_2 ^ (x * y).

axiom G_T_pow_mult :
 forall (x, y:int),  (g_T ^ x) ^ y = g_T ^ (x * y).

axiom G_2_log_pow_1 :
 forall (g_1': G_2), g_1 ^ G_2_log(g_1') = g_1'.

axiom G_1_log_pow_2 :
 forall (g_2': G_1), g_2 ^ G_1_log(g_2') = g_2'.

axiom G_T_log_pow :
 forall (g_T':G_T), g_T ^ G_T_log(g_T') = g_T'.

axiom G_2_pow_mod_1 :
 forall (z:int), g_1 ^ (z%%q_2) = g_1 ^ z.

axiom G_1_pow_mod_2 :
 forall (z:int), g_2 ^ (z%%q_1) = g_2 ^ z.

axiom G_T_pow_mod :
 forall (z:int), g_T ^ (z%%q_T) = g_T ^ z.

axiom mod_add :
 forall (x,y:int), (x%%q + y)%%q = (x + y)%%q.

axiom mod_small :
 forall (x:int), 0 <= x => x < q => x%%q = x.

axiom mod_sub :
 forall (x, y:int), (x%%q - y)%%q = (x - y)%%q.

axiom mod_bound :
 forall (x:int), 0 <= x%%q && x%%q < q.

pop Rand_exp : () -> (int).
pop Rand_G_1 : () -> (G_1).
pop Rand_G_2 : () -> (G_2).

(* axiom Rand_G_1_exp_def() : x = Rand_G_1_exp() ~ y = [0..q-1] : true ==> x = y. *)
axiom Rand_G_1_def() : x = Rand_G_1() ~ y = Rand_exp() : true ==> x = g_2 ^ y.

axiom Rand_G_2_def() : x = Rand_G_2() ~ y = Rand_exp() : true ==> x = g_1 ^ y.

adversary Adv (adv_public_key_1 : G_2, adv_public_key_2 : int) : (message * G_1) {message -> G_1; (message) -> G_1; (message) -> int}.

game blsfullMODEL_EF = {
  var sk1 : int
  var pk1 : G_2
  var var3 : int
  var queried : message list
  var count_Hash : int
  var count_testFunction2 : int
  var count_Sign : int
  var count_Verify : int
  var rand_oracle : (message, G_1) map

  fun Hash(m : message) : G_1 = {
    count_Hash = count_Hash + 1;
    if(!in_dom(m, rand_oracle)) {
      rand_oracle[m] = Rand_G_1();
    }
    return rand_oracle[m];
  }

  fun Sign(M : message) : G_1 = {
    var sigsig : G_1;
    var sig2 : G_1;
    var sig : G_1;
    var output : G_1;
    var var27 : int;
    count_Sign = count_Sign + 1;
    sig = Hash(M);
    sigsig = (sig ^ sk1);
    sig2 = Hash(M);
    var27 = testFunction3();
    output = sigsig;
    queried = M :: queried;
    return output;
  }

  fun testFunction2(M : message) : int = {
    var testVariable3 : G_1;
    var output : int;
    var hhh : G_1;
    var hhh1 : G_1;
    count_testFunction2 = count_testFunction2 + 1;
    hhh = Hash(M);
    hhh1 = (hhh ^ var3);
    testVariable3 = (hhh1 ^ sk1);
    output = var3;
    return output;
  }

  abs A = Adv{Hash, Sign, testFunction2}

  fun Verify(M : message, sig : G_1) : bool = {
    var h : G_1;
    var output : bool;
    var var4 : G_1;
    count_Verify = count_Verify + 1;
    h = Hash(M);
    if((e(h, pk1) = e(sig, g_1))) {
      output = true;
    }
    else {
      output = false;
    }
    output = (e(h, pk1) = e(sig, g_1));
    var4 = (g_2 ^ var3);
    return output;
  }

  fun Init() : bool = {
    var var5 : int;
    var var333 : G_2;
    var x : int;
    count_testFunction2 = 0;
    count_Hash = 0;
    count_Sign = 0;
    count_Verify = 0;
    var333 = Rand_G_2();
    x = Rand_exp();
    pk1 = (g_1 ^ x);
    sk1 = x;
    var3 = Rand_exp();
    var5 = testFunction3();
    rand_oracle = empty_map;
    queried = [];
    return true;
  }

  fun Main() : bool = {
    var M : message;
    var sig : G_1;
    var v : bool;
    var dummy : bool;

    dummy = Init();
    (M, sig) = A(pk1, var3);

    v = Verify(M, sig);
    return v && !mem(M, queried);
  }
}.
