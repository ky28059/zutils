open To_prop
open Typectx
open Sugar
module Nt = Normalty

let rec layout_nt_to_rocq wrap (ty : Nt.t) =
  let wrapped s = if wrap then "(" ^ s ^ ")" else s in
  match ty with
  | Ty_var x -> x
  | Ty_constructor ("bool", _) -> "Prop" (* Map bools to `Prop`s *)
  | Ty_constructor ("int", _) -> "Z" (* Map ints to `Stdlib.BinInt.Z`s *)
  | Ty_constructor (name, args) ->
    if List.length args > 0 then
      wrapped @@ String.concat " " @@ name :: List.map (layout_nt_to_rocq true) args
    else
      name
  | Ty_arrow (lty, rty) -> wrapped @@
    spf "%s -> %s" (layout_nt_to_rocq false lty) (layout_nt_to_rocq false rty) (* TODO? *)
  | Ty_poly (var, ty') -> wrapped @@
    spf "forall {%s : Type}, %s" var @@ layout_nt_to_rocq false ty'
  (* TODO: record types *)
  | _ -> "unknown"

let layout_nt_to_rocq = layout_nt_to_rocq false

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
  let preamble = "From Stdlib Require Import BinInt." in
  let content = spf "%s\n\n%s\n\n%s\n\n%s"
    preamble
    (layout_primitives_to_rocq ctx)
    (layout_axioms_to_rocq axioms)
    (layout_query_to_rocq prop)
  in
  Out_channel.with_open_text "/tmp/query.v" (fun oc ->
    Out_channel.output_string oc content;
    Out_channel.flush oc
  );
  Printf.printf "Wrote proof file to /tmp/query.v\n"
