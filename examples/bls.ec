prover alt-ergo, cvc3.

type group.
type message.
type key_pair.
type sk.
type pk.

cnst g : group.
cnst n : int.
cnst dummy : message.
cnst q : int.

op [^] : (group, int) -> group as group_pow.
op [*] : (group, group) -> group as group_mul.
op e : (group, group) -> group as group_pair.
op groupOp : (group, group) -> group.

axiom group_exp_0 : forall (x : group), x ^ 1 = x.
axiom group_exp_S : forall (x : group, k : int), k > 1 => x ^ k = groupOp(x, x^(k-1)).

axiom bilinear_map_0 : forall (x : group, a : int), e(x ^ a, x) = e(x, x) ^ a.
axiom bilinear_map_1 : forall (x : group, b : int), e(x, x ^ b) = e(x, x) ^ b.
axiom bilinear_map_2 : forall (x : group, y : group, a : int, b : int), e(x ^ a, y ^ b) = e(x, y) ^ (a * b).


