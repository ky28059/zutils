open Typectx
open Sugar
open Ast
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

let layout_const_to_rocq (const : constant) =
  match const with
  | U -> "unit"
  | B b -> if b then "True" else "False"
  | I i -> string_of_int i
  | C c -> spf "\"%c\"%%char" c
  | S s -> spf "\"%s\"%%string" s
  | F f -> spf "%f%%float" f (* TODO *)

let rec layout_lit_to_rocq wrap (lit : Nt.t lit) =
  let wrapped s = if wrap then "(" ^ s ^ ")" else s in
  let layout_tl w t = layout_lit_to_rocq w t.x in
  match lit with
  | AC c -> layout_const_to_rocq c
  | AVar { x; _ } -> x
  | ATu tl -> spf "(%s)" @@ String.concat ", " @@ List.map (layout_tl false) tl
  (* TODO: AProj, ARecord, AField? *)
  (* TODO: better infix op handling? *)
  | AAppOp ({ x = "=="; _ }, [l; r]) -> wrapped @@ spf "%s = %s" (layout_tl true l) (layout_tl true r)
  | AAppOp ({ x = "!="; _ }, [l; r]) -> wrapped @@ spf "%s <> %s" (layout_tl true l) (layout_tl true r)
  | AAppOp ({ x = "<"; _ }, [l; r]) -> wrapped @@ spf "%s < %s" (layout_tl true l) (layout_tl true r)
  | AAppOp ({ x = "<="; _ }, [l; r]) -> wrapped @@ spf "%s <= %s" (layout_tl true l) (layout_tl true r)
  | AAppOp ({ x = ">"; _ }, [l; r]) -> wrapped @@ spf "%s > %s" (layout_tl true l) (layout_tl true r)
  | AAppOp ({ x = ">="; _ }, [l; r]) -> wrapped @@ spf "%s >= %s" (layout_tl true l) (layout_tl true r)
  | AAppOp ({ x = "+"; _ }, [l; r]) -> wrapped @@ spf "%s + %s" (layout_tl true l) (layout_tl true r)
  | AAppOp ({ x = "-"; _ }, [l; r]) -> wrapped @@ spf "%s - %s" (layout_tl true l) (layout_tl true r)
  | AAppOp ({ x = "mod"; _ }, [l; r]) -> wrapped @@ spf "%s mod %s" (layout_tl true l) (layout_tl true r)
  | AAppOp (ft, tl) -> wrapped @@
    String.concat " " @@ ft.x :: List.map (layout_tl true) tl
  | _ -> "unknown"

let layout_lit_to_rocq = layout_lit_to_rocq false

let rec layout_prop_to_rocq wrap (prop : Nt.t prop) =
  let wrapped s = if wrap then "(" ^ s ^ ")" else s in
  match prop with
  | Lit { x; _ } -> layout_lit_to_rocq x
  | Implies (lp, rp) -> wrapped @@
    spf "%s -> %s" (layout_prop_to_rocq false lp) (layout_prop_to_rocq false rp)
  (* TODO ite? *)
  | Not p -> spf "~%s" @@ layout_prop_to_rocq true p
  | And pl -> wrapped @@
    String.concat " /\\ " @@ List.map (layout_prop_to_rocq true) pl
  | Or pl -> wrapped @@
    String.concat " \\/ " @@ List.map (layout_prop_to_rocq true) pl
  | Iff (lp, rp) -> wrapped @@
    spf "%s <-> %s" (layout_prop_to_rocq false lp) (layout_prop_to_rocq false rp)
  | Forall { qv = { x; ty }; body } -> wrapped @@
    spf "forall (%s : %s), %s" x (layout_nt_to_rocq ty) (layout_prop_to_rocq false body)
  | Exists { qv = { x; ty }; body } -> wrapped @@
    spf "exists (%s : %s), %s" x (layout_nt_to_rocq ty) (layout_prop_to_rocq false body)
  | _ -> "unknown"

let layout_prop_to_rocq = layout_prop_to_rocq false

let mk_signature_module (ctx : Nt.t ctx) axioms = (* TODO: indent? *)
  let defs = String.concat "\n" @@ List.map
    (fun { x; ty } -> spf "  Parameter %s : %s." x @@ layout_nt_to_rocq ty)
    @@ ctx_to_list ctx in
  let axs = String.concat "\n" @@ List.map
    (fun (name, _, prop) -> spf "  Axiom %s : %s." name @@ layout_prop_to_rocq prop)
    axioms in
  spf "Module Type Signatures\n%s\nEnd Signatures."
    @@ defs ^ "\n\n" ^ axs

let mk_axioms_module (_ctx : Nt.t ctx) axioms = (* TODO: indent? *)
  let axs = String.concat "\n" @@ List.map
    (fun (name, _, prop) -> spf "  Lemma %s : %s. Admitted." name @@ layout_prop_to_rocq prop)
    axioms in
  spf "Module Axioms : Signatures\n%s\nEnd Axioms."
    @@ "(* ... *)" ^ "\n\n" ^ axs (* TODO: hard-coded definitions *)

let mk_goal_module prop =
  spf "Module Goal.\n  Import Axioms.\n\n  Theorem goal : %s.\n  Proof.\n    (* ... *)\n  Qed.\nEnd Goal."
    @@ layout_prop_to_rocq prop

let dump_unsat (ctx: Nt.t ctx) axioms prop =
  let imports = String.concat "\n" [
    "From Stdlib Require Import BinInt.";
    "From Stdlib Require Import String.";
    "From Stdlib Require Import Ascii.";
    "From Stdlib Require Import Floats.";
    "Open Scope Z_scope."
  ] in
  let content = String.concat "\n\n" [
    imports;
    mk_signature_module ctx axioms;
    mk_axioms_module ctx axioms;
    mk_goal_module prop
  ] in
  Out_channel.with_open_text "/tmp/query.v" (fun oc -> (* TODO: take file path as arg? *)
    Out_channel.output_string oc content;
    Out_channel.flush oc
  );
  Printf.printf "Wrote proof file to /tmp/query.v\n"
