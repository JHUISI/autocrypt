(* prover alt-ergo, cvc3. *)

type G_1.
type G_T.
type message.
type key_pair.
type sk.
type pk.

cnst g_1_i : G_1.
cnst g_T_i : G_T.
cnst g : G_1.
cnst n : int.
cnst dummy : message.
cnst q : int.

op [*] : (G_1, G_1) -> G_1 as G_1_mul.
op [^] : (G_1, int) -> G_1 as G_1_pow.

op [*] : (G_T, G_T) -> G_T as G_T_mul.
op [^] : (G_T, int) -> G_T as G_T_pow.

op e : (G_1, G_1) -> G_T as G_1_pair.

axiom G_1_mult_1 : forall (x : G_1), x * g_1_i = x.
axiom G_1_exp_0 : forall (x : G_1), x ^ 0 = g_1_i.
axiom G_1_exp_S : forall (x : G_1, k : int), k > 0 => x ^ k = x * (x^(k-1)).

axiom G_T_mult_1 : forall (x : G_T), x * g_T_i = x.
axiom G_T_exp_0 : forall (x : G_T), x ^ 0 = g_T_i.
axiom G_T_exp_S : forall (x : G_T, k : int), k > 0 => x ^ k = x * (x^(k-1)).


axiom bilinearity : forall (x : G_1, y : G_1, a : int, b : int), e(x ^ a, y ^ b) = e(x, y) ^ (a * b).

adversary A (g : G_1, x : G_T) : bool {}.

cnst a : int.
cnst b : int.

game G3 = {

  abs A = A{}

  fun Main() : G_T = {
    var ret : G_T;
    ret = e(g^a, g^b);
    return ret;
  }

  fun Experiment() : bool = {
    var x : G_T;
    var decision : bool;

    x = Main();
    decision = A(g, x);
    return (decision = true);
  }
}.

game G4 = G3 
where Main = {
    var ret : G_T;
    ret = (e(g, g))^(b * a);
    return ret;
}.
 

equiv g3_g4_equiv: G3.Main ~ G4.Main : true ==> ={res}.
trivial.
save.

equiv g3_g4_equiv_exp: G3.Experiment ~ G4.Experiment : true ==> ={res}.
call.
call using g3_g4_equiv.
