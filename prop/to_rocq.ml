open Sugar
open Ast
module Nt = Normalty

let rec layout_nt_to_rocq wrap bool_as_prop (ty : Nt.t) =
  let wrapped s = if wrap then "(" ^ s ^ ")" else s in
  match ty with
  | Ty_var x -> x
  | Ty_constructor ("bool", _) -> if bool_as_prop then "Prop" else "bool" (* Map bools to `Prop`s *)
  | Ty_constructor ("int", _) -> "Z" (* Map ints to `Stdlib.BinInt.Z`s *)
  | Ty_constructor (name, args) ->
    if List.length args > 0 then
      wrapped @@ String.concat " " @@ name :: List.map (layout_nt_to_rocq true false) args
    else
      name
  | Ty_arrow (lty, rty) -> wrapped @@
    spf "%s -> %s" (layout_nt_to_rocq false false lty) (layout_nt_to_rocq false true rty) (* TODO? *)
  | Ty_poly (var, ty') -> wrapped @@
    spf "forall {%s : Type}, %s" var @@ layout_nt_to_rocq false bool_as_prop ty'
  (* TODO: record types *)
  | _ -> "unknown"

let layout_nt_to_rocq = layout_nt_to_rocq false false

let layout_const_to_rocq (const : constant) bool_as_prop =
  match const with
  | U -> "unit"
  | B b -> if bool_as_prop
    then if b then "True" else "False"
    else if b then "true" else "false"
  | I i -> string_of_int i
  | C c -> spf "\"%c\"%%char" c
  | S s -> spf "\"%s\"%%string" s
  | F f -> spf "%f%%float" f (* TODO *)

let rec layout_lit_to_rocq wrap bool_as_prop (lit : Nt.t lit) =
  let wrapped s = if wrap then "(" ^ s ^ ")" else s in
  let layout_tl w t = layout_lit_to_rocq w bool_as_prop t.x in
  match lit with
  | AC c -> layout_const_to_rocq c bool_as_prop
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
    String.concat " " @@ ft.x :: List.map (fun t -> layout_lit_to_rocq true false t.x) tl
  | _ -> "unknown"

let layout_lit_to_rocq = layout_lit_to_rocq false true

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
