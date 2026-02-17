open To_prop
open Typectx
open Sugar
module Nt = Normalty

let rec layout_nt_to_rocq (ty : Nt.t) =
  match ty with
  | Ty_var x -> x
  | Ty_constructor ("bool", _) -> "Prop" (* Map bools to `Prop`s *)
  | Ty_constructor (name, args) ->
    String.concat " " @@ name :: List.map layout_nt_to_rocq args
  | Ty_arrow (lty, rty) -> spf "%s -> %s" (layout_nt_to_rocq lty) (layout_nt_to_rocq rty)
  | Ty_poly (var, ty') -> spf "forall {%s : Type}, %s" var @@ layout_nt_to_rocq ty'
  (* TODO: record types *)
  | _ -> "unknown" 

let layout_primitives_to_rocq (ctx : Nt.t ctx) =
  String.concat "\n" @@ List.map
    (fun { x; ty } -> spf "Axiom %s : %s." x @@ layout_nt_to_rocq ty)
    @@ ctx_to_list ctx

let layout_axioms_to_rocq axioms =
  String.concat "\n" @@ List.map
    (fun (name, _, prop) -> spf "Lemma %s : %s. Admitted." name @@ layout_prop_to_coq prop)
    axioms

let layout_query_to_rocq prop =
  spf "Theorem goal : %s.\nProof.\n  (* ... *)\nQed.\n" @@ layout_prop_to_coq prop

let dump_unsat (ctx: Nt.t ctx) axioms prop =
  let content = spf "%s\n\n%s\n\n%s"
    (layout_primitives_to_rocq ctx)
    (layout_axioms_to_rocq axioms)
    (layout_query_to_rocq prop)
  in
  Out_channel.with_open_text "/tmp/query.v" (fun oc ->
    Out_channel.output_string oc content;
    Out_channel.flush oc
  );
  Printf.printf "Wrote proof file to /tmp/query.v\n"
