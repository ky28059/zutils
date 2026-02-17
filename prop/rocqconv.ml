open To_prop
open Typectx
open Sugar
module Nt = Normalty

(* TODO: dump to file *)
let dump_primitives (ctx : Nt.t ctx) =
  List.iter
    (fun { x; ty } -> Printf.printf "Axiom %s : %s.\n" x @@ Nt.layout_nt ty)
    @@ ctx_to_list ctx

(* TODO: dump to file*)
let dump_axioms axioms =
  List.iter
    (fun (name, _, prop) -> Printf.printf "Lemma %s : %s. Admitted.\n" name @@ layout_prop_to_coq prop)
    axioms

(* TODO: dump to file*)
let dump_query prop =
  Printf.printf "Theorem goal : %s.\nProof.\n  (* ... *)\nQed.\n" @@ layout_prop_to_coq prop
