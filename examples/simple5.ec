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

game simple5 = simple3
    var j : int

    where incrementCounter = {
        (* var j : int = [0..q]; *)
        var retVal : int;
        k=1;

        if (k = j) {
            retVal = 5;
        }
        else {
            retVal = 6;
        }

        return retVal;
    }

    and Main = {
        var retVal : int;
        j=1;
        k=2;
        retVal = A(5);
        return retVal;
    }.

(*
equiv simple3IC_simple4IC : simple3.incrementCounter ~ simple4.incrementCounter: true ==> ={res}.
trivial.
*)

equiv simple3Inc_simple5Inc : simple3.incrementCounter ~ simple5.incrementCounter: j{2}=1 ==> ={res}.
sp.
simpl.
equiv simple3Main_simple5Main : simple3.Main ~ simple5.Main: true ==> ={res}.

call (k{2}=j{2} => ={IncrementCounter.res}).
trivial.

game simple5 = simple3
    where incrementCounter = {
        k = k + 1;
        return 6;
    }

    and Main = {
        var retVal : int;

        retVal = A(5);
        return retVal;
    }.

equiv simple3Main_simple5Main: simple3.Main ~ simple5.Main: true ==> ={res}.
call.
trivial.



