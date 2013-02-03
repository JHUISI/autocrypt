cnst q : int.

adversary A(x:int) : int {int -> int}.

game simple3 = {
   var k : int

   fun incrementCounter(b:int) : int = {
       k = k + 1;
       return 5;
   }

   abs A  = A {incrementCounter}

   fun Main() : int = {
       var retVal : int;

       retVal = A(5);
       return retVal;
   }
}.

game simple4 = simple3
    where incrementCounter = {
        var j : int = [0..q];
        var retVal : int;

        k = k + 1;
        if (k = j) {
            retVal = 6;
        }
        else {
            retVal = 5;
        }

        return retVal;
    }

    and Main = {
        var retVal : int;

        retVal = A(5);
        return retVal;
    }.

equiv simple3IC_simple4IC : simple3.incrementCounter ~ simple4.incrementCounter: true ==> ={res}.
trivial.

equiv simple3Main_simple4Main : simple3.Main ~ simple4.Main: true ==> ={res}.
call.
trivial.