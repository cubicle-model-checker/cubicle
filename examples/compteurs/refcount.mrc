type resource 
type process

const resource null

module S = Set<type process>

var array(resource, bool) valid = mk_array[resource](false)
var array(resource, int) count 
var array(process, resource) ref = mk_array[process](null)
var array(resource, S.t) handles

transition create (resource r)
require (r != null)
require (!valid[r])
{
  valid[r] := true;
  count[r] := 0;
  handles[r] := S.empty;
}

transition destroy (resource r)
require (r != null)
require (valid[r])
require (count[r] = 0)
{
  valid[r] := false;
}

transition allocate (process p, resource r)
require (valid[r])
require (ref[p] = null)
{
  ref[p] := r;
  count[r] := count[r] + 1;
  handles[r] := S.add(p, handles[r]);
}

transition free (process p)
require (ref[p] != null)
{
  var resource r = ref[p];
  ref[p] := null;
  count[r] := count[r] - 1;
  handles[r] := S.remove(p, handles[r]);
}


def bool prop = 
  forall (process p) (ref[p] != null => valid[ref[p]])

def bool refs_non_zero = 
  forall (process p) (ref[p] != null => count[ref[p]] > 0)

def bool count_eq_card =
  forall 
    (resource r) 
    (r != null  && valid[r] => count[r] = S.cardinality(handles[r]))

def bool ref_in_set =
  forall (process p) (ref[p] != null => S.mem (p, handles[ref[p]]))

def bool in_set_is_ref =
  forall 
    (process p, resource r)
    (r != null && valid[r] && S.mem (p, handles[r]) => ref[p] = r)

goal main = invariant prop assuming refs_non_zero
goal sir  = invariant in_set_is_ref
goal ris  = invariant ref_in_set assuming prop
goal rcc  = invariant count_eq_card assuming ref_in_set, in_set_is_ref
goal rnz  = formula (count_eq_card && prop && ref_in_set => refs_non_zero)
