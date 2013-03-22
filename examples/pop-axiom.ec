(* this file contains some examples of how one can write axioms and
   asymmetric specifications for probabilistic operators *)

(* here is symmetric encryption *)

type key.
type cipher.
type plain = int.

pop makeKey : () -> key.
pop encrypt : (key, plain) -> cipher.
op decrypt : (key, cipher) -> plain.

(* asymmetric specification for working with first *or* second program *)

aspec crypt_single(k : key, p : plain) :
  c = encrypt(k, p) : true ==> decrypt(k, c) = p.

(* rule for working with both programs *)

axiom crypt_both(k1, k2: key, p1, p2 : plain) :
  c1 = encrypt(k1, p1) ~ c2 = encrypt(k2, p2) :
  k1 = k2 && p1 = p2 ==> c1 = c2 && decrypt(k1, c1) = p1.

(* use in first program *)

game G1 = {
  fun Main() : bool = {
    var p, p' : plain;
    var k : key;
    var c : cipher;
    p = 10;
    k = makeKey();
    c = encrypt(k, p);
    p' = decrypt(k, c);
    return p = p';
  }
}.

game G2 = {
  fun Main() : bool = {
    return true;
  }
}.

equiv G1G2 : G1.Main ~ G2.Main : true ==> ={res}.
auto.
apply {1} : crypt_single(k{1}, p{1}).
simpl.
save.

(* use in second program *)

game G1' = {
  fun Main() : bool = {
    return true;
  }
}.

game G2' = {
  fun Main() : bool = {
    var p, p' : plain;
    var k : key;
    var c : cipher;
    p = 10;
    k = makeKey();
    c = encrypt(k, p);
    p' = decrypt(k, c);
    return p = p';
  }
}.

equiv G1'G2' : G1'.Main ~ G2'.Main : true ==> ={res}.
auto.
apply {2} : crypt_single(k{2}, p{2}).
simpl.
save.

(* use in both programs *)

game G3 = {
  fun Main() : bool * cipher = {
    var p, p' : plain;
    var k : key;
    var c : cipher;
    p = 10;
    k = makeKey();
    c = encrypt(k, p);
    p' = decrypt(k, c);
    return (p = p', c);
  }
}.

game G4 = {
  fun Main() : bool * cipher = {
    var p, p' : plain;
    var k : key;
    var c : cipher;
    p = 10;
    k = makeKey();
    c = encrypt(k, p);
    p' = decrypt(k, c);
    return (p = p', c);
  }
}.

equiv G3G4 : G3.Main ~ G4.Main : true ==> ={res} && fst(res{1}).
sp; rnd >>; wp.
(* so now we have assumptions

  k{2} = k{1} && p{2} = 10 && p{1} = 10

and have to prove

  (let res_L = (p{1} = decrypt (k{1},c{1}),c{1}) in
   res_L = (p{2} = decrypt (k{2},c{2}),c{2}) && fst (res_L)),

i.e., that

  p{1} = decrypt (k{1},c{1}) &&
  p{2} = decrypt (k{2},c{2}) &&
  c{1} = c{2} *)
apply : crypt_both(k{1}, k{2}, p{1}, p{2}).
(* here we get the postcondition

  ={k,p} &&
  (forall (c_R, c_L : cipher),
     c_L = c_R => decrypt (k{1},c_L) = p{1} =>
        (let res_L = (p{1} = decrypt (k{1},c_L),c_L) in
          res_L = (p{2} = decrypt (k{2},c_R),c_R) && fst (res_L)))

which must be proved from the precondition

  k{2} = k{1} && p{2} = 10 && p{1} = 10

Thus the conclusion

  res_L = (p{2} = decrypt (k{2},c_R),c_R) &&
  fst (res_L)

must be shown from

  k{2} = k{1}
  p{2} = 10
  p{1} = 10
  c_R, c_L : cipher
  c_L = c_R
  decrypt (k{1},c_L) = p{1}
  res_L = (p{1} = decrypt (k{1},c_L),c_L)

Thus, we have to show

  p{1} = decrypt (k{1},c_L) &&
  p{2} = decrypt (k{2},c_R) &&
  c_L = c_R

which works.  In particular, the tactic gives us the knowledge
that c{1} = c{2}, i.e., that the encryptions (a probabilistic
operation) can be assumed to have worked out the same in
both programs.  This is like what happens with the rnd tactic: it's
how the tactics for random sampling work. *)
simpl.
save.
