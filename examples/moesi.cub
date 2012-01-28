type location = M | O | E | S | I

array A[proc] : location

init (z) { A[z] = I }

unsafe (z1 z2) { A[z1] = M &&  A[z2] = M }

transition t1 (x)
requires { A[x] = E }
{ A[j] := case | j = x : M | _ : A[j] ;}

transition t2 (x)
requires { A[x] = I }
{ A[j] := case 
           | j = x : S 
	   | A[j] = E : S 
	   | A[j] = M : O 
	   | _ : A[j] ; 
}
  
transition t3 (x)
requires { A[x] = S }
{ A[j] := case | j = x : E | _ : I ;}

transition t4 (x)
requires { A[x] = O }
{ A[j] := case | j = x : E | _ : I ; }

transition t5 (x)
requires { A[x] = I }
{ A[j] := case | j = x : E | _ : I; }


