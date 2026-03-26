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
  | AAppOp ({ x = "*"; _ }, [l; r]) -> wrapped @@ spf "%s * %s" (layout_tl true l) (layout_tl true r)
  | AAppOp ({ x = "/"; _ }, [l; r]) -> wrapped @@ spf "%s / %s" (layout_tl true l) (layout_tl true r)
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
    spf "%s -> %s" (layout_prop_to_rocq true lp) (layout_prop_to_rocq true rp)
  (* TODO ite? *)
  | Not p -> spf "~%s" @@ layout_prop_to_rocq true p
  | And pl -> wrapped @@
    String.concat " /\\ " @@ List.map (layout_prop_to_rocq true) pl
  | Or pl -> wrapped @@
    String.concat " \\/ " @@ List.map (layout_prop_to_rocq true) pl
  | Iff (lp, rp) -> wrapped @@
    spf "%s <-> %s" (layout_prop_to_rocq true lp) (layout_prop_to_rocq true rp)
  | Forall { qv = { x; ty }; body } -> wrapped @@
    spf "forall (%s : %s), %s" x (layout_nt_to_rocq ty) (layout_prop_to_rocq false body)
  | Exists { qv = { x; ty }; body } -> wrapped @@
    spf "exists (%s : %s), %s" x (layout_nt_to_rocq ty) (layout_prop_to_rocq false body)
  | _ -> "unknown"

let layout_prop_to_rocq = layout_prop_to_rocq false
