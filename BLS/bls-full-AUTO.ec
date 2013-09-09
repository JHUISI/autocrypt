prover alt-ergo, z3, cvc3.

type G_1.
type G_T.
type message.

cnst g_1_i : G_1.
cnst g_T_i : G_T.
cnst g_1 : G_1.
cnst g_2 : G_1.
cnst g_T : G_T.
cnst q_1 : int.
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

adversary Adv (adv_public_key_1 : G_1, adv_public_key_2 : int) : (message * G_1) {message -> G_1; (message) -> G_1; (message) -> G_1; () -> int; (message) -> G_1; () -> int; () -> int}.

game blsfullSYMM_EF = {
  var sk1 : int
  var pk1 : G_1
  var var3 : int
  var queried : message list
  var count_Hash : int
  var count_testFunction : int
  var count_testFunction3 : int
  var count_testFunction2 : int
  var count_testFunction5 : int
  var count_testFunction4 : int
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

  fun testFunction(M : message) : G_1 = {
    var hh1 : G_1;
    var hh : G_1;
    var output : G_1;
    var testVariable : G_1;
    count_testFunction = count_testFunction + 1;
    hh = Hash(M);
    hh1 = (hh ^ var3);
    testVariable = (hh1 ^ sk1);
    output = testVariable;
    return output;
  }

  fun testFunction3() : int = {
    var var7 : int;
    var var6 : int;
    var output : int;
    count_testFunction3 = count_testFunction3 + 1;
    var6 = Rand_G_1_exp();
    var7 = testFunction4();
    output = var6;
    return output;
  }

  fun testFunction2(M : message) : G_1 = {
    var testVariable3 : G_1;
    var output : G_1;
    var hhh : G_1;
    var hhh1 : G_1;
    count_testFunction2 = count_testFunction2 + 1;
    hhh = Hash(M);
    hhh1 = (hhh ^ var3);
    testVariable3 = (hhh1 ^ sk1);
    output = testVariable3;
    return output;
  }

  fun testFunction5() : int = {
    var var13 : int;
    var output : int;
    count_testFunction5 = count_testFunction5 + 1;
    var13 = Rand_G_1_exp();
    output = var13;
    return output;
  }

  fun testFunction4() : int = {
    var output : int;
    var var8 : int;
    var var12 : int;
    count_testFunction4 = count_testFunction4 + 1;
    var8 = Rand_G_1_exp();
    var12 = testFunction5();
    output = var8;
    return output;
  }

  abs A = Adv{Hash, Sign, testFunction, testFunction3, testFunction2, testFunction5, testFunction4}

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
    var x : int;
    count_testFunction = 0;
    count_testFunction3 = 0;
    count_testFunction2 = 0;
    count_testFunction5 = 0;
    count_testFunction4 = 0;
    count_Hash = 0;
    count_Sign = 0;
    count_Verify = 0;
    x = Rand_G_1_exp();
    pk1 = (g_1 ^ x);
    sk1 = x;
    var3 = Rand_G_1_exp();
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
