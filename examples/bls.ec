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

game BLS_EF = {
  var secret_key : int
  var rand_oracle : (message, G_1) map
  var queried : message list

  fun Hash(m : message) : G_1 = {
    if(!in_dom(m, rand_oracle)) {
      rand_oracle[m] = Rand_G_1();
    }
    return rand_oracle[m];
  }
  
  fun Sign(m : message) : G_1 = {
    var h : G_1;
    var s : G_1;
    h = Hash(m);
    s = h^secret_key;
    queried = m :: queried;
    return s;
  }

  abs A = Adv{Hash, Sign}

  fun Verify(m : message, s : G_1, pk : G_1) : bool = {
    var v : bool;
    var h : G_1;
    h = Hash(m);
    v = (e(h, pk) = e(s, g));
    return v;
  }

  fun Main() : bool = {
    var pk : G_1;    
    var m : message;
    var h : G_1;
    var s : G_1;
    var v : bool;
   
    secret_key = KG();
    pk = g^secret_key;
    rand_oracle = empty_map;
    queried = [];

    (m, s) = A(pk);

    v = Verify(m, s, pk);
    return v && !mem(m, queried);
  }
}.












(* Generic definition of CDH

Rules:

You cannot overwrite Main.  

You can change types that are not already defined like state and can
overwrite functions other than Main.
*)

type state.
cnst null_state : state.

game CDH_Generic = {
  var given_1 : G_1;
  var given_2 : G_1;

  fun Before(b : G_1) : (state * G_1) = {
    return (null_state, g_1_i);
  }

  fun After(t : state, m : message, s : G_1, b : G_1) : int = {
    return 0;
  }


  fun Hash(m : message) : G_1 = {
    return g_1_i;
  }
  
  fun Sign(m : message) : G_1 = {
    return g_1_i;
  }

  abs A = Adv{Hash, Sign}

  fun Main() : bool = {
    var secret : G_1;
    var pk : G_1;
    var m : message;
    var s : G_1;
    var trans : state;
    var a : int;
    var b : int;
    var guess : G_1;

    a = [0..q-1]
    b = [0..q-1]
    secret = g^(a*b)
    given_1 = g^a
    given_2 = g^b

    (trans, pk) = Before(given_1, given_2);
    (m, s)=A(pk);
    guess = After(trans, pk, m, s, given_1, given_2);

    return (guess = secret);
  }
}.


(* for each message we can create a random z
then hash(m) = m^z
sign(m) = pk^z
*)