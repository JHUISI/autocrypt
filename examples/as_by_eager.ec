(* example involving redundant hashing, where the proof is done using
   "by eager" *)

prover "alt-ergo". timeout 2.

adversary A(b : bool) : bool { bool -> bool}.

(* we want to prove G1 and G2 equivalent

   this can't be done using the call tactic to handle the call to A,
   as the only invariants that play well with Hash are at least as
   strong as ={hash}; and simpl is of no help, because it can't tell
   that the presence of b in hash is undetectable by A

   instead, we'll have to use "by eager" *)

game G1 = {
  var hash : (bool, bool)map

  fun Hash(x : bool) : bool = {
    var x' : bool;
    if (!in_dom(x, hash)) {
      x' = {0, 1};
      hash[x] = x';
    }
    return hash[x];
  }

  abs A = A{Hash}

  fun Main() : bool = {
    var b, b', b'' : bool;
    hash = empty_map;
    b = {0, 1};
    b' = Hash(b);  (* b' not used *)
    b'' = A(b);
    return b'';
  }
}.

game G2 = G1
  where Main = {
    var b, b'' : bool;
    hash = empty_map;
    b = {0, 1};
    (* the call to Hash is missing! *)
    b'' = A(b);
    return b'';
  }.

game G4 = G1
  var b, b', b'' : bool (* by eager makes these be global *)

  where Main = {
    hash = empty_map;
    (* unless we add the following initializations, the second part of
       the by eager fails *)
    b' = true;
    b'' = true;
    (* end of seemingly unnecessary initializations *)
    b = {0, 1};
    b'' = A(b);
    (* inlining of Hash(b) -- by eager issues error message if we don't
       inline *)
    if (!in_dom(b, hash)) {
      b' = {0, 1};
      hash[b] = b';
    }
    (* had to obliterate possible assignment to b', or first part of
       by eager fails *)
    b' = true;
    (* end of inlining *)
    return b'';
  }.

game G3 = G4
  where Main = {
    hash = empty_map;
    (* questionable initializations *)
    b' = true;
    b'' = true;
    (* end of questionable initializations *)
    b = {0, 1};
    (* inlining of Hash(b) *)
    if (!in_dom(b, hash)) {
      b' = {0, 1};
      hash[b] = b';
    }
    b' = true;
    (* end of inlining *)
    b'' = A(b);
    return b'';
  }.

(* here is the step using "by eager"; must put G4 then G3 *)

equiv G4_G3_Main : G4.Main ~ G3.Main : true ==> ={res}
by eager
{ 
  if (!in_dom(b, hash)) {
    b' = {0, 1};
    hash[b] = b';
  }
  b' = true;
}.
proof.
(* first part of by eager -- showing that redundant hash commutes with
   call of Hash, as would be done (maybe many times) by A *)
case : x = b.
if.
rnd >>.
sp.
condf.
trivial.
condf {1}.
sp.
condf {2}.
simpl.
(* x <> b *)
derandomize.
swap {1} 2 -1.
rnd >>.
rnd >>.
wp.
simpl.
save.
(* second part of by eager: initialization *)
trivial.
(* third part of by eager: finalization *)
simpl.
save.

claim G3_G4 : G3.Main[res] = G4.Main[res]
using G4_G3_Main.

equiv G1_G3_Main : G1.Main ~ G3.Main : true ==> ={res}.
proof.
sp.
rnd >>.
inline Hash.
sp.
if.
rnd >>.
auto.
(* boolean false *)
auto.
save.

claim G1_G3 : G1.Main[res] = G3.Main[res]
using G1_G3_Main.

equiv G2_G4_Main : G2.Main ~ G4.Main : true ==> ={res}.
proof.
sp.
rnd >>.
app 1 1 ={hash, b''}.
auto.
(* after app *)
if {2}; trivial.
save.

claim G2_G4 : G2.Main[res] = G4.Main[res]
using G2_G4_Main.

(* our overall goal: *)

claim G1_G2 : G1.Main[res] = G2.Main[res].
