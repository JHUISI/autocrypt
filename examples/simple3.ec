cnst q : int.

adversary A(x:int) : int {int -> int}.

game simple3 = {
   var k : int

   fun incrementCounter(b:int) : int = {
       var retVal : int;

       k = k + 1;
       retVal = 5;
       return retVal;
   }

   abs A  = A {incrementCounter}

   fun Main() : int = {
       var a : int;
       var retVal : int;

       a = 5;
       k = k + 1;
       retVal = A(a);
       return retVal;
   }

}.

game simple4 = simple3
    where incrementCounter = {
        var j : int = [0..q];
        var retVal : int;

        k = k + 1;
        if (k = j) {
            retVal = 5;
        }
        else {
            retVal = 5;
        }

        return retVal;
    }

    (* abs A = A{} *)

    and Main = {
        var a : int;
        var retVal : int;

        a = 5;
        k = k + 1;
        retVal = A(a);
        return retVal;
    }.

equiv simple3IC_simple4IC : simple3.incrementCounter ~ simple4.incrementCounter: true ==> ={res}.
trivial.

equiv simple3Main_simple4Main : simple3.Main ~ simple4.Main: true ==> ={res}.
call.
trivial.
trivial.