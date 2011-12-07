
module type EXTENDED_Polynome = sig
  include Polynome.T
  val poly_of : r -> t
  val alien_of : t -> r
end

module Make 
  (X : Sig.X)
  (P : EXTENDED_Polynome with type r = X.r) 
  : Sig.RELATION with type r = X.r
