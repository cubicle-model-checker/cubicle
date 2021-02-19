type 'a abstract

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end
  
module Make 
  (X : ALIEN) : Sig.THEORY with type r = X.r and type t = X.r abstract
