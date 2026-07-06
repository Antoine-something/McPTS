
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val solution_right : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let solution_right _ x _ =
  x

(** val simplification_heq : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2 **)

let simplification_heq _ _ h =
  h __
