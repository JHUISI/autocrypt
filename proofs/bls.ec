prover alt-ergo, z3, cvc3.

timeout 10.

type G_1.
type G_T.
type message.

cnst g_1_i : G_1.
cnst g_T_i : G_T.
cnst g_1 : G_1.
cnst g_T : G_T.
cnst q : int.
cnst limit_Hash : int.

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
(* axiom non_degenerate : !(e(g_1, g_1) = g_T_i). *)

axiom G_1_pow_add : 
 forall (x, y:int), g_1 ^ (x + y) = g_1 ^ x * g_1 ^ y.

axiom G_T_pow_add : 
 forall (x, y:int), g_T ^ (x + y) = g_T ^ x * g_T ^ y.

axiom G_1_pow_mult :
 forall (x, y:int),  (g_1 ^ x) ^ y = g_1 ^ (x * y).

axiom G_T_pow_mult :
 forall (x, y:int),  (g_T ^ x) ^ y = g_T ^ (x * y).

axiom G_1_log_pow : 
 forall (g_1':G_1), g_1 ^ G_1_log(g_1') = g_1'.

axiom G_T_log_pow : 
 forall (g_T':G_T), g_T ^ G_T_log(g_T') = g_T'.

axiom G_1_pow_mod : 
 forall (z:int), g_1 ^ (z%%q) = g_1 ^ z.

axiom G_T_pow_mod : 
 forall (z:int), g_T ^ (z%%q) = g_T ^ z.

axiom mod_add : 
 forall (x,y:int), (x%%q + y)%%q = (x + y)%%q.

axiom mod_small : 
 forall (x:int), 0 <= x => x < q => x%%q = x.

axiom mod_sub : 
 forall (x, y:int), (x%%q - y)%%q = (x - y)%%q. 

axiom mod_bound : 
 forall (x:int), 0 <= x%%q && x%%q < q. 


pop Rand_exp   : () -> (int).
pop Rand_G_1 : () -> (G_1).

(* axiom Rand_G_1_exp_def() : x = Rand_G_1_exp() ~ y = [0..q-1] : true ==> x = y. *)
axiom Rand_G_1_def() : x = Rand_G_1() ~ y = Rand_exp() : true ==> x = g_1 ^ y.

adversary Adv (adv_public_key : G_1) : (message * G_1) {(message) -> G_1; message -> G_1}.

game BLS_EF = {
  var secret_key : int
  var rand_oracle : (message, G_1) map
  var queried : message list
  var count_Hash : int
  var count_Sign : int
  var count_Verify : int

  fun Hash(m : message) : G_1 = {
    count_Hash = count_Hash + 1;
    if(!in_dom(m, rand_oracle)) {
      rand_oracle[m] = Rand_G_1();
    }
    return rand_oracle[m];
  }
  
  fun Sign(m : message) : G_1 = {
    var h : G_1;
    var s : G_1;
    count_Sign = count_Sign + 1;
    h = Hash(m);
    s = h^secret_key;
    queried = m :: queried;
    return s;
  }

  abs A = Adv{Hash, Sign}

  fun Verify(m : message, s : G_1, pk : G_1) : bool = {
    var v : bool;
    var h : G_1;
    count_Verify = count_Verify + 1;
    h = Hash(m);
    v = (e(h, pk) = e(s, g_1));
    return v;
  }

  fun Init() : bool = {
    count_Hash = 0;
    count_Sign = 0;
    count_Verify = 0;
    secret_key = Rand_exp();
    rand_oracle = empty_map;
    queried = [];
    return true;
  }

  fun Main() : bool = {
    var pk : G_1;    
    var m : message;
    var h : G_1;
    var s : G_1;
    var v : bool;
    var dummy : bool;

    dummy=Init();
    pk = g_1^secret_key;

    (m, s) = A(pk);

    v = Verify(m, s, pk);
    return v && !mem(m, queried);
  }
}.


game G_Inv_Sign = BLS_EF

var hashes : (message, G_1) map
var sigs : (message, G_1) map
var given_1 : G_1 (* analogous to the public key *)

  where Init = {
    count_Hash = 0;
    count_Sign = 0;
    count_Verify = 0;
    secret_key = Rand_exp();
    rand_oracle = empty_map;
    queried = [];
    hashes = empty_map;
    sigs = empty_map;
 
    return true;
  }

  and Hash = {
    var exp : int;

    count_Hash = count_Hash + 1;
    if(!in_dom(m, hashes)) {
      exp=Rand_exp();

      hashes[m]=g_1^exp;      
      sigs[m]=given_1^exp;
    }
    return hashes[m];
  }

  and Sign = {
    var h : G_1;
    var s : G_1;
    h = Hash(m);
    s = sigs[m];
    queried = m :: queried;
    return s;
  }

  and Main = {
    var pk : G_1;
    var m : message;
    var h : G_1;
    var s : G_1;
    var v : bool;
    var dummy : bool;

    dummy=Init();
    pk = g_1^secret_key;
    given_1 = pk;

    (m, s) = A(pk);

    v = Verify(m, s, pk);
    return v && !mem(m, queried);
  }
.

(* prove that the output of the hash functions is still the same *)
equiv Mod_Hash : BLS_EF.Hash ~ G_Inv_Sign.Hash :    
  ={m,secret_key,queried,count_Hash} && rand_oracle{1}=hashes{2} && given_1{2}=g_1^secret_key{2} &&
    (forall (m_0:message), in_dom(m_0,hashes{2}) => 
      sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}) ==>
  ={res,secret_key,queried,count_Hash} && rand_oracle{1}=hashes{2} && given_1{2}=g_1^secret_key{2} &&
    (forall (m_0:message), in_dom(m_0,hashes{2}) =>
      sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}).
sp.
if.
derandomize.
wp.
apply : Rand_G_1_def().
simpl.
trivial.
save.

(* Next we need to prove that the output of the Sign function is still the same *)
equiv Mod_Sign : BLS_EF.Sign ~ G_Inv_Sign.Sign :
  ={m,secret_key,queried,count_Hash} && rand_oracle{1}=hashes{2} && given_1{2}=g_1^secret_key{2} &&
  (forall (m_0:message), in_dom(m_0,hashes{2}) =>
    sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}) ==>
  ={res,secret_key,queried,count_Hash} && rand_oracle{1}=hashes{2} && given_1{2}=g_1^secret_key{2} &&
  (forall (m_0:message), in_dom(m_0,hashes{2}) =>
    sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}).

wp.
swap{1} 2.
app 1 1 
  (in_dom(m{1}, rand_oracle{1}) &&
    in_dom(m{2}, hashes{2}) &&
    h{1}=rand_oracle{1}[m{1}] &&
    h{2}=hashes{2}[m{2}]) &&
    ={m,secret_key,queried,count_Hash} &&
    rand_oracle{1} = hashes{2} &&
    given_1{2}=g_1^secret_key{2} &&
    (forall (m_0 : message),
      in_dom (m_0,hashes{2}) =>
      sigs{2}[m_0] = hashes{2}[m_0] ^ secret_key{2}).
inline.
sp.
if.
derandomize.
wp.
apply : Rand_G_1_def().
simpl.

wp.
simpl.

trivial.
save.

equiv Mod_Verify : BLS_EF.Verify ~ G_Inv_Sign.Verify : ={m, s, pk, secret_key, queried, count_Hash} && rand_oracle{1}=hashes{2} && given_1{2}=g_1^secret_key{2} &&
    (forall (m_0:message), in_dom(m_0,hashes{2}) => 
      sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}) ==> ={res,queried, count_Hash}.
wp.
call using Mod_Hash.
wp.
trivial.
save.

equiv Mod_A : BLS_EF.A ~ G_Inv_Sign.A : 
={adv_public_key, secret_key, queried, count_Hash} && rand_oracle{1}=hashes{2} && given_1{2}=g_1^secret_key{2} &&
(forall (m_0:message), in_dom(m_0,hashes{2}) => 
      sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2})
  ==>
  ={res, secret_key, queried, count_Hash} && rand_oracle{1}=hashes{2} && given_1{2}=g_1^secret_key{2} &&
  (forall (m_0:message), in_dom(m_0,hashes{2}) => 
      sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}) by auto(={secret_key, queried, count_Hash} && rand_oracle{1}=hashes{2} && given_1{2}=g_1^secret_key{2} &&
  (forall (m_0:message), in_dom(m_0,hashes{2}) => 
      sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2})).
    

equiv e_G_Inv_Sign_unlimited : BLS_EF.Main ~ G_Inv_Sign.Main : true ==> ={res}.
call using Mod_Verify.
call using Mod_A.
wp.
inline.
wp.
rnd.
trivial.
save.

equiv e_G_Inv_Sign : BLS_EF.Main ~ G_Inv_Sign.Main : true ==> ={res} && (count_Hash{1} <= limit_Hash)=(count_Hash{2} <= limit_Hash).
call using Mod_Verify.
call using Mod_A.
wp.
inline.
wp.
rnd.
trivial.
save.

(*
   we made it so we can "sign" using the public key only
   now we need to hijack one hash at random 
*)

(* previous defs 
  where Init = {
    secret_key = Rand_G_1_exp();
    rand_oracle = empty_map;
    queried = [];
    hashes = empty_map;
    sigs = empty_map;
 
   return true;
  }

  and Hash = {
    var exp : int;

    if(!in_dom(m, hashes)) {
      exp=[0..q];

      hashes[m]=g_1^exp;      
      sigs[m]=hashes[m]^secret_key;
    }
    return hashes[m];
  }

  and Sign = {
    var h : G_1;
    var s : G_1;
    h = Hash(m);
    s = sigs[m];
    queried = m :: queried;
    return s;
  }

  and Main = {
    var pk : G_1;    
    var m : message;
    var h : G_1;
    var s : G_1;
    var v : bool;
    var dummy : bool;

    dummy=Init();
    pk = g^secret_key;
    given_1 = pk;

    (m, s) = A(pk);

    v = Verify(m, s, pk);
    return v && !mem(m, queried);
  }
*)

game G_Choose_One = G_Inv_Sign
  var n_inject : int
  var m_inject : message
  var m_adv : message
  var enum : (message, int) map
  var given_2 : G_1
  var bad : bool

  where Init = {
    enum = empty_map;
    count_Hash = 0;
    rand_oracle = empty_map;
    queried = [];
    hashes = empty_map;
    sigs = empty_map;
    n_inject = [1..limit_Hash];
    return true;
  }

  and Hash = {
    var exp : int;
    count_Hash = count_Hash + 1;

    if(!in_dom(m, hashes)) {
      enum[m] = count_Hash;
      if(count_Hash = n_inject) {
        m_inject = m;
        (* hashes[m] = given_2 *)
      } (* else { *)
        exp=Rand_exp();
        hashes[m]=g_1^exp;      
        sigs[m]=given_1^exp;
      (* } *)
    }
    return hashes[m];
  }

  and Sign = {
    var h : G_1;
    var s : G_1;
    h = Hash(m);
    s = sigs[m];
    queried = m :: queried;
    if (enum[m]=n_inject) {
      bad = true;
    }
    return s;
  }

  and Main = {
    var pk : G_1;    
    var s : G_1;
    var v : bool;
    var dummy : bool;
    var b : int;

    dummy=Init();
    secret_key = Rand_exp();
    b = Rand_exp();
    given_1 = g_1^secret_key;
    given_2 = g_1^b;

    pk = given_1;

    (m_adv, s) = A(pk);

    v = Verify(m_adv, s, pk);
    return v && !mem(m_adv, queried);
  }
.

(* prove that the output of the hash functions is still the same *)
equiv Mod_Hash2 : G_Inv_Sign.Hash ~ G_Choose_One.Hash:    
  ={m,secret_key,queried,count_Hash,sigs,hashes,rand_oracle,given_1}
  ==>
  ={res,secret_key,queried,count_Hash,sigs,hashes,rand_oracle,given_1}.
derandomize.
app 2 2 ={m,secret_key,queried,count_Hash,sigs,hashes,rand_oracle,given_1,exp_0}.
wp.
rnd.
trivial.
if.
swap{2} 5.
if{2}.
wp.
trivial.
wp.
trivial.
trivial.
save.

(* Next we need to prove that the output of the Sign function is still the same *)
equiv Mod_Sign2 : G_Inv_Sign.Sign ~ G_Choose_One.Sign :
  ={m,secret_key,queried,count_Hash,sigs,hashes,rand_oracle,given_1}
  ==>
  ={res,secret_key,queried,count_Hash,sigs,hashes,rand_oracle,given_1}.
wp.
call using Mod_Hash2.  
trivial.
save.

equiv Mod_A2 : G_Inv_Sign.A ~ G_Choose_One.A : 
  ={adv_public_key,secret_key,queried,count_Hash,sigs,hashes,rand_oracle,given_1}
  ==>
  ={res,secret_key,queried,count_Hash,sigs,hashes,rand_oracle,given_1} by auto(={secret_key,queried,count_Hash,sigs,hashes,rand_oracle,given_1}).

equiv Mod_Verify2 : G_Inv_Sign.Verify ~ G_Choose_One.Verify : 
  ={m,s,pk,secret_key,queried,count_Hash,sigs,hashes,rand_oracle,given_1}
  ==>
  ={res,secret_key,queried,count_Hash,sigs,hashes,rand_oracle,given_1}.
wp.
call using Mod_Hash2.
wp.
trivial.
save.


equiv E_G_Choose_One_unlimited : G_Inv_Sign.Main ~ G_Choose_One.Main : true ==> ={res}.
call using Mod_Verify2.
call using Mod_A2.
wp.
inline.
wp.
derandomize.
wp.
rnd{2}.
rnd.
trivial.
save.

equiv E_G_Choose_One : G_Inv_Sign.Main ~ G_Choose_One.Main : true ==> ={res} && (count_Hash < limit_Hash){1} = (count_Hash < limit_Hash){2}.
call using Mod_Verify2.
call using Mod_A2.
wp.
inline.
derandomize.
wp.
swap{2} -1.
rnd.
rnd{2}.
rnd{2}.
trivial.
save.

equiv E_Bad_Insig_Hash : G_Choose_One.Hash ~ G_Choose_One.Hash : 
 ={m,bad,given_2,enum,m_adv,m_inject,n_inject,given_1,sigs,hashes,count_Verify,count_Sign,count_Hash,queried,rand_oracle,secret_key} &&
(forall (m4:message), !in_dom(m4, hashes){1} => !mem(m4, queried){1}) &&
((exists (m3:message), (enum[m3] = n_inject && mem(m3, queried)){1}) <=> bad{1})
==>
 ={res,bad,given_2,enum,m_adv,m_inject,n_inject,given_1,sigs,hashes,count_Verify,count_Sign,count_Hash,queried,rand_oracle,secret_key} &&
(forall (m4:message), !in_dom(m4, hashes){1} => !mem(m4, queried){1}) &&
((exists (m3:message), (enum[m3] = n_inject && mem(m3, queried)){1}) <=> bad{1}).
derandomize.
rnd>>.
wp.
trivial.
save.

equiv E_Bad_Insig_Sign : G_Choose_One.Sign ~ G_Choose_One.Sign :  
 ={m,bad,given_2,enum,m_adv,m_inject,n_inject,given_1,sigs,hashes,count_Verify,count_Sign,count_Hash,queried,rand_oracle,secret_key} &&
(forall (m4:message), !in_dom(m4, hashes){1} => !mem(m4, queried){1}) &&
((exists (m3:message), (enum[m3] = n_inject && mem(m3, queried)){1}) <=> bad{1})
==>
 ={res,bad,given_2,enum,m_adv,m_inject,n_inject,given_1,sigs,hashes,count_Verify,count_Sign,count_Hash,queried,rand_oracle,secret_key} &&
(forall (m4:message), !in_dom(m4, hashes){1} => !mem(m4, queried){1}) &&
((exists (m3:message), (enum[m3] = n_inject && mem(m3, queried)){1}) <=> bad{1}).
inline.
derandomize.
rnd>>.
app 5 5 ( ={s,m,bad,given_2,enum,m_adv,m_inject,n_inject,given_1,sigs,hashes,count_Verify,count_Sign,count_Hash,queried,rand_oracle,secret_key} && forall (m4:message), !in_dom(m4, hashes){1} => !mem(m4, queried){1}) && in_dom(m, hashes){1} &&
((exists (m3:message), (enum[m3] = n_inject && mem(m3, queried)){1}) <=> bad{1}).
wp.
trivial.
wp.
trivial.
save.

equiv E_Bad_Insig_A : G_Choose_One.A ~ G_Choose_One.A :  
 ={adv_public_key,bad,given_2,enum,m_adv,m_inject,n_inject,given_1,sigs,hashes,count_Verify,count_Sign,count_Hash,queried,rand_oracle,secret_key} && (forall (m4:message), !in_dom(m4, hashes){1} => !mem(m4, queried){1}) &&
((exists (m3:message), (enum[m3] = n_inject && mem(m3, queried)){1}) <=> bad{1})
==>
 ={res,bad,given_2,enum,m_adv,m_inject,n_inject,given_1,sigs,hashes,count_Verify,count_Sign,count_Hash,queried,rand_oracle,secret_key} &&
(forall (m4:message), !in_dom(m4, hashes){1} => !mem(m4, queried){1}) &&
((exists (m3:message), (enum[m3] = n_inject && mem(m3, queried)){1}) <=> bad{1}) by auto (
 ={bad,given_2,enum,m_adv,m_inject,n_inject,given_1,sigs,hashes,count_Verify,count_Sign,count_Hash,queried,rand_oracle,secret_key} &&
(forall (m4:message), !in_dom(m4, hashes){1} => !mem(m4, queried){1}) &&
((exists (m3:message), (enum[m3] = n_inject && mem(m3, queried)){1}) <=> bad{1})
).

equiv E_Bad_Insig : G_Choose_One.Main ~ G_Choose_One.Main : 
true 
==> 
(count_Hash<limit_Hash && enum[m_adv]=n_inject && res){1} => (count_Hash<limit_Hash && enum[m_adv]=n_inject && res && (!bad)){2}.
admit.
save.

game G_Violate = G_Choose_One
  where Hash = {
    var exp : int;
    count_Hash = count_Hash + 1;

    if(!in_dom(m, hashes)) {
      enum[m] = count_Hash;
      if(count_Hash = n_inject) {
        m_inject = m;
        hashes[m] = given_2;
      } else {
        exp=Rand_exp();
        hashes[m]=g_1^exp;      
        sigs[m]=given_1^exp;
      }
    }
    return hashes[m];
  }

  and Main = {
    var pk : G_1;    
    var s : G_1;
    var v : bool;
    var dummy : bool;
    var b : int;
    var secret : G_1;
    var dummy2 : G_1;

    dummy=Init();
    secret_key = Rand_exp();
    b = Rand_exp();
    given_1 = g_1^secret_key;
    given_2 = g_1^b;
    secret = g_1^(secret_key*b);
    
    pk = given_1;

    (m_adv, s) = A(pk);

    dummy2 = Hash(m_adv);
    return (s = secret);
  }
.

(* Prove the output of the hash functions is the same when count isn't n_inject *)

(* Prove that m!=m_inject implies that the output of Sign is the same *)





(* step 1: prove that condition C implies that verify succeeds *)

equiv E_G_Violate : G_Choose_One.Main ~ G_Violate.Main : true ==> ((count_Hash < limit_Hash){1} = (count_Hash < limit_Hash){2}) && ((enum[m_adv]=n_inject){1} = (enum[m_adv]=n_inject){2}) && ={bad} && (((count_Hash < limit_Hash){1} && (count_Hash < limit_Hash){2} && (enum[m_adv]=n_inject){1} && (enum[m_adv]=n_inject){2} && (!bad{1}) && (!bad{2})) => (res{1}=>res{2})).
admit.

(*
app 7 8 ={hashes,n_inject,m_adv,s} && ((count_Hash+1 < limit_Hash){1} = (count_Hash+1 < limit_Hash){2}) && ((enum[m_adv]=n_inject){1} = (enum[m_adv]=n_inject){2}) && (((count_Hash < limit_Hash){1} && (count_Hash < limit_Hash){2} && (enum[m_adv]=n_inject){1} && (enum[m_adv]=n_inject){2}) => (in_dom(m_adv, hashes){1} && in_dom(m_adv, hashes){2} && ={s})).

(*(((s=hashes[m_adv]^secret_key){1} && (!mem(m_adv, queried)){1})=>(s=secret){2}))). *)
admit.
inline.

sp.
case : (in_dom(m,hashes)).
condf.
wp.
trivial.
simpl.

*)
(*
HERE

condf.
admit.
condt.
wp.
sp.
if{2}.
wp.
rnd{1}.
trivial.

sp.
if{1}.
wp.
rnd{1}.
wp.
trivial.

rand.

case : ((enum[m_adv] = n_inject) &&
          count_Hash < limit_Hash).



          enum{1}[m_adv{1}] = n_inject{1} =>
          enum{2}[m_adv{2}] = n_inject{2} )).
condf{1}.
wp.
trivial.



(count_Hash < limit_Hash){1} = (count_Hash < limit_Hash){2}) && ((enum[m_adv]=n_inject){1} = (enum[m_adv]=n_inject){2}) && (((count_Hash < limit_Hash){1} && (count_Hash < limit_Hash){2} && (enum[m_adv]=n_inject){1} && (enum[m_adv]=n_inject){2})((s=hashes[m_adv]^secret_key && count_Hash < limit_Hash && enum[m_adv]=n_inject && in_dom(m_adv, hashes)){1} = (s=hashes[m_adv]^secret_key && count_Hash<limit_Hash && enum[m_adv]=n_inject && in_dom(m_adv, hashes)){2}) && (count_Hash>n_inject){2}.
case : (count_Hash < limit_Hash).

*)
save.


(*
claim C_neg1 : BLS_EF.Main[res && count_Hash<limit_Hash] <= BLS_EF.Main[res]
same.

claim C_0 : BLS_EF.Main[res] = G_Choose_One.Main[res]
admit.

claim C_1_5 : G_Choose_One.Main[res && count_Hash<limit_Hash && enum[m_adv]=n_inject] <= G_Choose_One.Main[res]
same.
*)

(* need to update proofs to include count_Hash<limit_Hash *)
claim C_0 : BLS_EF.Main[count_Hash<limit_Hash && res] = G_Choose_One.Main[count_Hash<limit_Hash && res]
admit.

claim C_1_1 : G_Choose_One.Main[true] = 1%r
compute.

claim C_junk555 : G_Choose_One.Main[enum[m_adv]<limit_Hash && enum[m_adv]>0 && enum[m_adv]=n_inject] = 1%r
admit.

claim C_1_2 : G_Choose_One.Main[count_Hash<limit_Hash && enum[m_adv]=n_inject && res] = G_Choose_One.Main[count_Hash<limit_Hash && res && enum[m_adv]=n_inject]
same.

claim C_1_3 :  G_Choose_One.Main[enum[m_adv]<limit_Hash && enum[m_adv]>0] * 1%r/(2+limit_Hash)%r <= G_Choose_One.Main[enum[m_adv]<limit_Hash && enum[m_adv]>0 && enum[m_adv]=n_inject]
compute.


(* need to figure out how to get this to work *)
claim C_1_5 : G_Choose_One.Main[count_Hash<limit_Hash && res] * 1%r/(2+limit_Hash)%r <= G_Choose_One.Main[count_Hash<limit_Hash && res && enum[m_adv]=n_inject]
compute.

claim C_1_0 : G_Choose_One.Main[count_Hash<limit_Hash && enum[m_adv]=n_inject && !bad && res] <= G_Violate.Main[count_Hash<limit_Hash && enum[m_adv]=n_inject && !bad && res]
using E_G_Violate.

(* need to figure this out, how to deal with !bad being insignificant *)
claim C_1_1 : G_Choose_One.Main[count_Hash<limit_Hash && enum[m_adv]=n_inject && res] <= G_Choose_One.Main[count_Hash<limit_Hash && enum[m_adv]=n_inject && (!bad) && res]
using E_Bad_Insig.


claim C_1_2 : G_Choose_One.Main[count_Hash<limit_Hash && res] * 1%r/(1+limit_Hash)%r <= G_Choose_One.Main[count_Hash<limit_Hash && enum[m_adv]=n_inject && (!bad) && res].

(*
claim C_1 : G_Choose_One.Main[count_Hash<limit_Hash && enum[m_adv]=n_inject && res] <= G_Violate.Main[count_Hash<limit_Hash && enum[m_adv]=n_inject && res]
same.
*)

claim C_2 : G_Violate.Main[count_Hash < limit_Hash && enum[m_adv]=n_inject && (!bad) && res] <= G_Violate.Main[res]
same.

claim C_1_7 : BLS_EF.Main[count_Hash<limit_Hash && res] * 1%r/(1+limit_Hash)%r <= G_Choose_One.Main[count_Hash<limit_Hash && enum[m_adv]=n_inject && res]. 



claim C_3 : G_Choose_One.Main[count_Hash<limit_Hash && enum[m_adv]=n_inject && (!bad) && res] <= G_Violate.Main[res].

claim C_4 : BLS_EF.Main[count_Hash<limit_Hash && res] * 1%r/(1+limit_Hash)%r <= G_Violate.Main[res].





All TRASH from here


            



(res && count_Hash < limit_Hash && enum[m_adv]=n_inject){1} = (res && !mem(m_adv, queried) && count_Hash < limit_Hash && enum[m_adv]=n_inject){2}.


equiv E_G_Violate : G_Choose_One.Main ~ G_Violate.Main : true ==> (res && count_Hash < limit_Hash && enum[m_adv]=n_inject){1} = (res && !mem(m_adv, queried) && count_Hash < limit_Hash && enum[m_adv]=n_inject){2}.
app 7 8 ((s=hashes[m_adv]^secret_key && count_Hash < limit_Hash && enum[m_adv]=n_inject && in_dom(m_adv, hashes)){1} = (s=hashes[m_adv]^secret_key && count_Hash < limit_Hash && enum[m_adv]=n_inject && in_dom(m_adv, hashes)){2}) && (count_Hash>n_inject){2}.
admit.


inline.
condf{1}.
wp.
trivial.


ifsync{1} 7.

(* need to create cases for the conditions of our postcondition *)



(* need to add something about whether we chose the right thing to hijack *)



HERE



claim C_Basic : G_Choose_One.Main[res] = G_Inv_Sign.Main[res]
using E_G_Choose_One.


claim C_Hash_Lim : G_Choose_One.Main[res && count_Hash < limit_Hash] = G_Inv_Sign.Main[res && count_Hash < limit_Hash]
using E_G_Choose_One.

claim Test1 : G_Inv_Sign.Main[res && count_Hash < limit_Hash] <= G_Inv_Sign.Main[res]
same.

claim Test2 : G_Choose_One.Main[res && count_Hash < limit_Hash] <= G_Inv_Sign.Main[res].

equiv E_G_Choose_One_Prob : G_Choose_One.Main ~ G_Choose_One.Main : true ==> (enum[m_adv] > 0 && enum[m_adv] < count_Hash){1}.
admit.

claim C_test5 : G_Choose_One.Main[enum[m_adv] > 0 && enum[m_adv] < count_Hash] = 1%r
using E_G_Choose_One_Prob.

claim C_Hash_Lim2 : G_Choose_One.Main[res && count_Hash<limit_Hash && n_inject=enum[m_adv]] >= (1%r)/((limit_Hash+5)%r) * G_Inv_Sign.Main[res && count_Hash < limit_Hash]
using E_G_Choose_One_Prob.

claim C_Hash_Lim2 : G_Choose_One.Main[res && count_Hash<limit_Hash && m_inject=m_adv] >= (1%r)/(limit_Hash%r) * G_Inv_Sign.Main[res && count_Hash < limit_Hash]
compute.

note that adv_m in_dom thing (because verify calls hash and verify gets called)

we need to complete this proof
then we can make a probability claim about m_inject = enum[adv_m]
completing the proof will first require adding enum
we may need to rework hash count a little to so that it doesn't count repeated queries.  Hopefully we can avoid that though.




(* in_dom => i > 0 and i < q *)



(* here *)

derandomize.
wp.
rnd.
simpl.
trivial.
save.

(* Next we need to prove that the output of the Sign function is still the same *)
equiv Mod_Sign : BLS_EF.Sign ~ G_Inv_Sign.Sign :
  ={m,secret_key,queried,count_Hash} && rand_oracle{1}=hashes{2} &&
  (forall (m_0:message), in_dom(m_0,hashes{2}) =>
    sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}) ==>
  ={res,secret_key,queried,count_Hash} && rand_oracle{1}=hashes{2} &&
  (forall (m_0:message), in_dom(m_0,hashes{2}) =>
    sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}).

wp.
swap{1} 2.
app 1 1 
  (in_dom(m{1}, rand_oracle{1}) &&
    in_dom(m{2}, hashes{2}) &&
    h{1}=rand_oracle{1}[m{1}] &&
    h{2}=hashes{2}[m{2}]) &&
    ={m,secret_key,queried,count_Hash} &&
    rand_oracle{1} = hashes{2} &&
    (forall (m_0 : message),
      in_dom (m_0,hashes{2}) =>
      sigs{2}[m_0] = hashes{2}[m_0] ^ secret_key{2}).
inline.
sp.
if.
derandomize.
wp.
apply : Rand_G_1_def().
simpl.

wp.
simpl.

trivial.
save.

equiv Mod_Verify : BLS_EF.Verify ~ G_Inv_Sign.Verify : ={m, s, pk, secret_key, queried, count_Hash} && rand_oracle{1}=hashes{2} &&
    (forall (m_0:message), in_dom(m_0,hashes{2}) => 
      sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}) ==> ={res,queried, count_Hash}.
wp.
call using Mod_Hash.
wp.
trivial.
save.

equiv Mod_A : BLS_EF.A ~ G_Inv_Sign.A : 
={adv_public_key, secret_key, queried, count_Hash} && rand_oracle{1}=hashes{2} &&
(forall (m_0:message), in_dom(m_0,hashes{2}) => 
      sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2})
  ==>
  ={res, secret_key, queried, count_Hash} && rand_oracle{1}=hashes{2} &&
  (forall (m_0:message), in_dom(m_0,hashes{2}) => 
      sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}) by auto(={secret_key, queried, count_Hash} && rand_oracle{1}=hashes{2} &&
  (forall (m_0:message), in_dom(m_0,hashes{2}) => 
      sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2})).
    


equiv e_G_Choose_One : G_Inv_Sign.Main ~ G_Choose_One.Main : true ==> ={res} && (count_Hash{1} <= limit_Hash)=(count_Hash{2} <= limit_Hash).
call using Mod_Verify.
call using Mod_A.
wp.
inline.
wp.
rnd.
trivial.
save.


(* prove this is equivalent to the other game when ...the bad
   thing doesn't happen *)


call using Mod_Hash.
trivial.
simpl.


wp.
inline.
app 1 1  (={m_0,m,secret_key,queried} && m_0{1}=m{1} && m_0{2}=m{2} && rand_oracle{1} = hashes{2}) && (forall (m_0:message), in_dom(m_0,hashes{2}) => sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2}).
trivial.
if.
swap{2} -1.
app 1 2 (={m_0,m,secret_key,queried} && m_0{1} = m{1} && m_0{2} = m{2} && rand_oracle{1} = hashes{2} && rand_oracle{1}[m_0{1}]=hashes{2}[m_0{2}] && (forall (m_0:message), in_dom(m_0,hashes{2}) => sigs{2}[m_0]=hashes{2}[m_0]^secret_key{2})).
derandomize.
wp.
apply : Rand_G_1_def().
simpl.

wp.
simpl.
wp.
trivial.



app 0 0 m{2}=m_0{2} && ={m_0,m,secret_key,queried} &&
         rand_oracle{1} = hashes{2} &&
          rand_oracle{1}[m_0{1}] = hashes{2}[m_0{2}]
.

admit.
trivial.

app 2 
wp.
sp.
if.
derandomize.
wp.

simpl.
trivial.



equiv Mod_Sigs : BLS_EF.Sign ~ G_Inv_Sign.Hash : 
={m,secret_key,queried} && rand_oracle{1}=hashes{2} ==> res{1}==sigs{2}[m{2}].

equiv Mod_Sign : BLS_EF.Sign ~ G_Inv_Sign.Sign : 
={m,secret_key,queried} && rand_oracle{1}=hashes{2} ==> ={res,secret_key,queried} && rand_oracle{1}=hashes{2}.



game Inject = BLS_EF
var j : int
var i : int
var mess_num : (message, int) map

where Hash = {
    if(!in_dom(m, rand_oracle)) {
      rand_oracle[m] = Rand_G_1();
      mess_num[m]=i;
      i=i+1;
    }
    return rand_oracle[m];
}

and Init = {
  secret_key = Rand_G_1_exp();
  rand_oracle = empty_map;
  mess_num = empty_map;
  queried = [];
  i=0;
  j=[0..queries];
  return true;
}.
  
equiv



game Test1 = {
  fun Main() : G_1 = {
    var ret : G_1;
    ret = Rand_G_1();
    return ret;
  }
}.

game Test2 = Test1

where Main = {
  var exp : int;
  exp = [0..q];

  return g_1^exp;
}.

equiv Test_equiv : Test1.Main ~ Test2.Main : true ==> ={res}.
apply : Rand_G_1_def().
simpl.
save.




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
    return (null_state, g_1);
  }

  fun After(t : state, m : message, s : G_1, b : G_1) : int = {
    return 0;
  }

  fun Hash(m : message) : G_1 = {
    return g_1;
  }
  
  fun Sign(m : message) : G_1 = {
    return g_1;
  }

  abs A = Adv{Hash, Sign}

  fun Main() : bool = {
    var secret : G_1;
    var pk : G_1;
    var m : message;
    var s : G_1;
    var trans : state;
    var a : int; (* these both must be thrown away *)
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

(* a is analogous to the key in our game *)

(* 
   a ~ secret key
   given_1 ~ public key
   given_2 ~ the hijacked message
*) 


Game CDH_BLS = CDH_Generic

var sigs : (message, G_1) map
var hashes : (message, G_1) map
var i : int
var j : int

where Before = {
  j=[0..queries];
  sigs=empty_map;
  hashes=empty_map;
  return (null_state, given_1);
}

where Hash = {
  var h : G_1;
  var exp : int;
 
  if(!in_dom(m, sigs)) {
    if(i=j) {
      hashes[m]=given_2
    } else {
      exp=Rand_G_1_exp();
      sigs[m]=given_1^exp;
      hashes[m]=g_1^exp;
    }
    i=i+1;
  }
  return hashes[m];
}

and Sign = {
  var h : G_1;
  h=Hash(m)
  return sigs[m];
}.

equiv CDH_BLS.Main ~ ...
