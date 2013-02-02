adversary A(x:int) : int {}.

game simple3 = {
   abs A = A{}

   fun Main() : int = {
       var a : int;
       var retVal : int;

       a = 5;
       retVal = A(a);
       return retVal;
   }

}.

game simple4 = simple3
    where Main = {
        var a : int;
        var retVal : int;

        a = 5;
        retVal = A(a);
        return retVal;
    }.

equiv simple3Main_simple4Main : simple3.Main ~ simple4.Main: true ==> ={res}.
call.
trivial.