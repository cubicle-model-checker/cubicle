let negate_cube_to_clause cube = 
  let l = cube.Cube.litterals in
  let l = SAtom.fold (
    fun a l -> SAtom.add (Atom.neg a) l
  ) l SAtom.empty in
  let v = cube.Cube.vars in
  Cube.create v l
