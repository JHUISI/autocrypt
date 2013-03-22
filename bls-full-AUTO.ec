prover alt-ergo, z3, cvc3.

type G_1.
type G_T.
type message.

cnst g_1_i : G_1.
cnst g_T_i : G_T.
cnst g : G_1.
cnst q : int.

op [*] : (G_1, G_1) -> G_1 as G_1_mul.
op [^] : (G_1, int) -> G_1 as G_1_pow.

op [*] : (G_T, G_T) -> G_T as G_T_mul.
op [^] : (G_T, int) -> G_T as G_T_pow.

op e : (G_1, G_1) -> G_T as G_1_pair.

(* pull in the axioms from ElGamal.  Note that G_1 and G_T have the same order (double check this). *)

axiom G_1_mult_1 : forall (x : G_1), x * g_1_i = x.
axiom G_1_exp_0 : forall (x : G_1), x ^ 0 = g_1_i.
axiom G_1_exp_S : forall (x : G_1, k : int), k > 0 => x ^ k = x * (x^(k-1)).

axiom G_T_mult_1 : forall (x : G_T), x * g_T_i = x.
axiom G_T_exp_0 : forall (x : G_T), x ^ 0 = g_T_i.
axiom G_T_exp_S : forall (x : G_T, k : int), k > 0 => x ^ k = x * (x^(k-1)).

axiom bilinearity : forall (x : G_1, y : G_1, a : int, b : int), e(x ^ a, y ^ b) = e(x, y) ^ (a * b).
axiom non_degenerate : !(e(g, g) = g_T_i).

pop KG   : () -> (int).
pop Rand_G_1 : () -> (G_1).


adversary Adv (adv_public_key : G_1) : (message * G_1) {message -> G_1; message -> G_1}.

game blsfull_EF = {
