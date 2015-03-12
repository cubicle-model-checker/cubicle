
exception Empty
(*exception Not_found*)

type 'a elt = Nil | Cell of 'a * 'a elt * 'a elt
type 'a t = { head : 'a elt; tail : 'a elt;  }

let empty = { head = Nil; tail = Nil }

let is_empty q = q.head = Nil

let push x q = (* add at head *)
  let new_head = match q.head with
    | Nil -> Cell (x, Nil, Nil)
    | Cell (y, next, prev) ->
        assert (next = Nil);
        let rec new_head = Cell (x, Nil, Cell (y, new_head, prev)) in
        new_head
  in
  let new_tail = match q.tail with
    | Nil -> new_head
    | Cell (y, Nil, prev) -> assert (prev = Nil); Cell (y, new_head, prev);
    | Cell (_, _, prev) -> assert (prev = Nil); q.tail
  in
  { head = new_head; tail = new_tail }

let pop q = (* remove from tail *)
  let pre_tail, x = match q.tail with
    | Nil -> assert (q.head = Nil); raise Empty
    | Cell (x, next, prev) -> assert (prev = Nil); next, x
  in
  let new_head, new_tail = match pre_tail with
    | Nil -> Nil, Nil
    | Cell (y, Nil, _) -> let elt = Cell (y, Nil, Nil) in elt, elt
    | Cell (y, next, _) -> q.head, Cell (y, next, Nil)
  in
  x, { head = new_head; tail = new_tail }

let iter f q = (* iter from head to tail *)
  let rec aux = function
    | Nil -> ()
    | Cell (x, _, prev) -> f x; aux prev
  in
  aux q.head

let rev_iter f q = (* iter from tail to head *)
  let rec aux = function
    | Nil -> ()
    | Cell (x, next, _) -> f x; aux next
  in
  aux q.tail

let fold_left f a q = (* fold from head to tail *)
  let rec aux a = function
    | Nil -> a
    | Cell (x, _, prev) -> aux (f a x) prev
  in
  aux a q.head

let fold_right f a q = (* fold from tail to head *)
  let rec aux a = function
    | Nil -> a
    | Cell (x, next, _) -> aux (f a x) next
  in
  aux a q.tail

let for_all p q =
  let rec aux = function
    | Nil -> true
    | Cell (x, _, prev) -> if p x then aux prev else false
  in
  aux q.head

let exists p q =
  let rec aux = function
    | Nil -> false
    | Cell (x, _, prev) -> if p x then true else aux prev
  in
  aux q.head

let find p q = (* find from head *)
  let rec aux = function
    | Nil -> raise Not_found
    | Cell (x, _, prev) -> if p x then x else aux prev
  in
  aux q.head

let rev_find p q = (* find from tail *)
  let rec aux = function
    | Nil -> raise Not_found
    | Cell (x, next, _) -> if p x then x else aux next
  in
  aux q.tail
