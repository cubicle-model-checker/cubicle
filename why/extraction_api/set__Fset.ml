module Make (O : Set.OrderedType) = struct
  module S = Set.Make (O)
         
  type 'a set = S.t
                  
  include S

end
