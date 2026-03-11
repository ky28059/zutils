open Typectx
open Sugar
open Front

let mk_signature_module preds axioms = (* TODO: indent? *)
  let types = String.concat "\n" @@ Rocqdefs.built_in_type_sigs in
  let defs = String.concat "\n" @@ List.map
    (fun { x; ty } -> spf "  Parameter %s : %s." x @@ layout_nt_to_rocq ty)
    preds in
  let axs = String.concat "\n" @@ List.map
    (fun (name, _, prop) -> spf "  Axiom %s : %s." name @@ layout_prop_to_rocq prop)
    axioms in
  spf "Module Type Signatures.\n%s\nEnd Signatures."
    @@ String.concat "\n\n" [types; defs; axs]

let mk_axioms_module preds axioms = (* TODO: indent? *)
  let layout_builtin { x; ty } =
    match Hashtbl.find_opt Rocqdefs.built_in_defs x with
    | Some x -> x
    | None -> spf "  Parameter %s : %s." x @@ layout_nt_to_rocq ty in
  let layout_axiom (name, _, prop) =
    match Hashtbl.find_opt Rocqdefs.built_in_proofs name with
    | Some x -> x
    | None -> spf "  Lemma %s : %s. Admitted." name @@ layout_prop_to_rocq prop in
  let types = String.concat "\n" Rocqdefs.built_in_type_defs in
  let defs = String.concat "\n" @@ List.map layout_builtin preds in
  let axs = String.concat "\n" @@ List.map layout_axiom axioms in
  spf "Module Axioms : Signatures.\n%s\nEnd Axioms."
    @@ String.concat "\n\n" [types; defs; axs]

let mk_goal_module prop =
  spf "Module Goal.\n  Import Axioms.\n\n  Theorem goal : %s.\n  Proof.\n    (* ... *)\n  Qed.\nEnd Goal.\n"
    @@ layout_prop_to_rocq prop

let dump_unsat (ctx: Nt.t ctx) axioms prop =
  let imports = String.concat "\n" [
    "From Stdlib Require Import BinInt.";
    "From Stdlib Require Import String.";
    "From Stdlib Require Import Ascii.";
    "From Stdlib Require Import Floats.";
    "Open Scope Z_scope."
  ] in
  let types = Rocqdefs.remove_builtins @@ ctx_to_list ctx in
  let content = String.concat "\n\n" [
    imports;
    mk_signature_module types axioms;
    mk_axioms_module types axioms;
    mk_goal_module prop
  ] in
  Out_channel.with_open_text "/tmp/query.v" (fun oc -> (* TODO: take file path as arg? *)
    Out_channel.output_string oc content;
    Out_channel.flush oc
  );
  Printf.printf "Wrote proof file to /tmp/query.v\n"
