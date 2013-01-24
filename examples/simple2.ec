(* ctrl-c, ctrl-n : step forward
   ctrl-c, ctrl u : step backward
   ctrl-s : search for a keyword
*)
 
cnst d : int.
(* axiom mod_small : forall(x:int, n:int), 0 <= x => x < n => x%n = x. *)

adversary A(x:int) : int {}.

game simple1 = {
   abs A = A{}

   fun Main() : int = {
       var a : int;
       var b : int;
       var c : int;
       
       a = [0 .. 5];
       b = (a + d) % 6;
       c = A(b);
       return c;
   }
}.

game simple2 = simple1
   where Main = {
       var a : int;
       var c : int;

       a = [0 .. 5];
       c = A(a);
       return c;
}.

equiv simple12 : simple1.Main ~ simple2.Main : true ==> ={res}.
call. (* removes call to the abstract procedure in each game. Result: changes post condition according to the specification of the procedure. Infers postcondition over abstract prodcedure which says that if inputs are equivalent and from the same distribution, then outputs are also equivalent. *) 
wp.
rnd ((a + d) % 6), ((a - d) % 6).
trivial.