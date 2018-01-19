/******************************************************************************
  A fragment of set-theory for finite sets  
******************************************************************************/

template <type value> Array
{
 /*****************************************************************************
   Theory Signature
 *****************************************************************************/

 // The type of sets with elements of type elem
 type t

 // The emptyset
 const t empty

 // Add an element to a set
 const t add (int, value x, t s)


 // Cardinality of a set
 const int cardinality (t s)

 /*****************************************************************************
   Axioms for set membership
 *****************************************************************************/
 
 axiom mem_empty = forall (elem e) (!(mem(e,empty)))

 axiom mem_add   = 
   forall 
     (elem x, elem y, t s) 
     (mem (x, add (y, s)) = (x = y || mem (x, s)))

 axiom mem_remove =
   forall
     (elem x, elem y, t s)
     (mem (x, remove(y, s)) = (x !=y && mem(x, s)))

 /*****************************************************************************
   Axioms for cardinality
 *****************************************************************************/

 axiom card_empty =
   cardinality(empty) = 0

 axiom card_zero =
   forall (t s) (cardinality(s) = 0 => s = empty)

 axiom card_non_negative =
   forall (t s) (cardinality(s) >= 0)

 axiom card_add =
   forall
     (elem x, t s)
     (cardinality(add(x, s)) = (mem(x, s) ? cardinality(s) : cardinality(s) + 1))

 axiom card_remove =
   forall
     (elem x, t s)
     (cardinality (remove(x, s)) = (mem(x, s) ? cardinality(s) - 1 : cardinality(s)))
}
