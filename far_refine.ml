let refine v1 t v2 =
  List.fold_left (
    fun acc cube ->
      (negate_cube_to_clause cube) :: acc
  ) [] v2.bads
      
