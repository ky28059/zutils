open To_prop
open Typectx
open Sugar
module Nt = Normalty

let rec layout_nt_to_rocq (ty : Nt.t) =
  match ty with
  | Ty_var x -> x
  | Ty_constructor ("bool", _) -> "Prop" (* Map bools to `Prop`s *)
  | Ty_constructor (name, args) ->
    spf "%s %s" name
    @@ String.concat " " @@ List.map layout_nt_to_rocq args
  | Ty_arrow (lty, rty) -> spf "%s -> %s" (layout_nt_to_rocq lty) (layout_nt_to_rocq rty)
  | Ty_poly (var, ty') -> spf "forall (%s : Type), %s" var @@ layout_nt_to_rocq ty'
  (* TODO: record types *)
  | _ -> "unknown" 

(* TODO: dump to file *)
let dump_primitives (ctx : Nt.t ctx) =
  List.iter
    (fun { x; ty } -> Printf.printf "Axiom %s : %s.\n" x @@ layout_nt_to_rocq ty)
    @@ ctx_to_list ctx

(* TODO: dump to file*)
let dump_axioms axioms =
  List.iter
    (fun (name, _, prop) -> Printf.printf "Lemma %s : %s. Admitted.\n" name @@ layout_prop_to_coq prop)
    axioms

(* TODO: dump to file*)
let dump_query prop =
  Printf.printf "Theorem goal : %s.\nProof.\n  (* ... *)\nQed.\n" @@ layout_prop_to_coq prop
