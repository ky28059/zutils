module Nt = Normalty
open Sugar

let built_in_type_sigs = [
  "Parameter tree : forall (a : Type), Type.";
  "Parameter rbtree : forall (a : Type), Type."
]

let built_in_type_defs = [
  {|
  Inductive tree' (a : Type) : Type :=
  | Leaf : tree' a
  | Node : a -> tree' a -> tree' a -> tree' a.
  Definition tree := tree'.
  |};
  {|
  Inductive rbtree' (a : Type) : Type :=
  | Rbtleaf : rbtree' a
  | Rbtnode : bool -> rbtree' a -> a -> rbtree' a -> rbtree' a.
  Definition rbtree := rbtree'.
  |}
]

let built_in_defs = Hashtbl.of_seq @@ List.to_seq [
  ("hd", {|
  Definition hd {a : Type} (l : list a) (n : a) : Prop :=
    match l with
    | nil => False
    | cons n' _ => n = n'
    end.
  |});
  ("tl", {|
  Definition tl {a : Type} (l : list a) (xs : list a) : Prop :=
    match l with
    | nil => False
    | cons _ xs' => xs = xs'
    end.
  |});
  ("len", {|
  Fixpoint len {a : Type} (l : list a) (n : Z) : Prop :=
    match l with
    | nil => n = 0
    | cons _ xs => n > 0 /\ len xs (n - 1)
    end.
  |});
  ("emp", {|
  Definition emp {a : Type} (l : list a) : Prop :=
    match l with
    | nil => True
    | cons _ _ => False
    end.
  |});
  ("list_mem", {|
  Fixpoint list_mem {a : Type} (l : list a) (x : a) : Prop :=
    match l with
    | nil => False
    | cons x' xs => (x = x') \/ list_mem xs x
    end.
  |});
  ("uniq", {|
  Fixpoint uniq {a : Type} (l : list a) : Prop :=
    match l with
    | nil => True
    | cons x xs => ~(list_mem xs x) /\ uniq xs
    end.
  |});
  ("sorted", {|
  Fixpoint sorted (l : list Z) : Prop :=
    match l with
    | nil => True
    | cons x nil => True
    | cons x xs =>
      match xs with
      | nil => True
      | cons y _ => x <= y /\ sorted xs
      end
    end.
  |});
  ("all_evens", {|
  Fixpoint all_evens (l : list Z) : Prop :=
    match l with
    | nil => True
    | cons x xs => (exists n, x = 2 * n) /\ all_evens xs
    end.
  |});
  ("depth", {|
  Fixpoint depth {a : Type} (t : tree a) (n : Z) : Prop :=
    match t with
    | Leaf _ => n = 0
    | Node _ _ l r => exists nl nr : Z, 
      depth l nl /\ depth r nr /\ n = Z.max nl nr + 1
    end.
  |});
  ("leaf", {|
  Definition leaf {a : Type} (t : tree a) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ _ _ _ => False
    end.
  |});
  ("root", {|
  Definition root {a : Type} (t : tree a) (x : a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ x' _ _ => x = x'
    end.
  |});
  ("lch", {|
  Definition lch {a : Type} (t : tree a) (l : tree a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ _ l1 _ => l1 = l
    end.
  |});
  ("rch", {|
  Definition rch {a : Type} (t : tree a) (r : tree a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ _ _ r1 => r1 = r
    end.
  |});
  ("tree_mem", {|
  Fixpoint tree_mem {a : Type} (t : tree a) (e : a) : Prop :=
    match t with
    | Leaf _ => False
    | Node _ v l r => v = e \/ tree_mem l e \/ tree_mem r e
    end.
  |});
  ("complete", {|
  Fixpoint complete {a : Type} (t : tree a) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ _ l r => complete l /\ complete r /\ (exists n, depth l n /\ depth r n)
    end.
  |});
  ("lower_bound", {|
  Fixpoint lower_bound (t : tree Z) (x : Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ y l r => x <= y /\ lower_bound l x /\ lower_bound r x
    end.
  |});
  ("upper_bound", {|
  Fixpoint upper_bound (t : tree Z) (x : Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ y l r => y <= x /\ upper_bound l x /\ upper_bound r x
    end.
  |});
  ("bst", {|
  Fixpoint bst (t : tree Z) : Prop :=
    match t with
    | Leaf _ => True
    | Node _ x l r => bst l /\ bst r /\ upper_bound l x /\ lower_bound r x
    end.
  |});
  ("num_black", {|
  Fixpoint num_black {a : Type} (t : rbtree a) (h : Z) : Prop :=
    match t with
    | Rbtleaf _ => h = 0
    | Rbtnode _ c l _ r =>
      if c then num_black l (h - 1) /\ num_black r (h - 1)
      else num_black l h /\ num_black r h
    end.
  |});
  ("rb_leaf", {|
  Definition rb_leaf {a : Type} (t : rbtree a) : Prop :=
    match t with
    | Rbtleaf _ => True
    | Rbtnode _ _ _ _ _ => False
    end.
  |});
  ("rb_root", {|
  Definition rb_root {a : Type} (t : rbtree a) (x : a) : Prop :=
    match t with
    | Rbtleaf _ => False
    | Rbtnode _ _ _ y _ => x = y
    end.
  |});
  ("rb_lch", {|
  Definition rb_lch {a : Type} (t : rbtree a) (l : rbtree a) : Prop :=
    match t with
    | Rbtleaf _ => False
    | Rbtnode _ _ l1 _ _ => l = l1
    end.
  |});
  ("rb_rch", {|
  Definition rb_rch {a : Type} (t : rbtree a) (r : rbtree a) : Prop :=
    match t with
    | Rbtleaf _ => False
    | Rbtnode _ _ _ _ r1 => r = r1
    end.
  |});
  ("no_red_red", {|
  Fixpoint no_red_red {a : Type} (t : rbtree a) : Prop :=
    match t with
    | Rbtleaf _ => True
    | Rbtnode _ c l _ r =>
      if negb c then no_red_red l /\ no_red_red r
      else
        match (l, r) with
        | (Rbtnode _ c' _ _ _, Rbtnode _ c'' _ _ _) =>
          (c' = false) /\ (c'' = false) /\ no_red_red l /\ no_red_red r
        | (Rbtnode _ c' _ _ _, Rbtleaf _) => (c' = false) /\ no_red_red l
        | (Rbtleaf _, Rbtnode _ c'' _ _ _) => (c'' = false) /\ no_red_red r
        | (Rbtleaf _, Rbtleaf _) => True
        end
    end.
  |});
  ("rb_root_color", {|
  Definition rb_root_color {a : Type} (t : rbtree a) (c : Prop) : Prop :=
    match t with
    | Rbtleaf _ => False
    | Rbtnode _ c1 _ _ _ => (c /\ c1 = true) \/ (~c /\ c1 = false)
    end.
  |})
]

let built_in_proofs = Hashtbl.of_seq @@ List.to_seq [
  ("list_emp_no_hd", {|
  Lemma list_emp_no_hd : forall (l : list Z), forall (x : Z), emp l -> ~hd l x.
  Proof.
    intros [| x'] x H.
    - intros [].
    - contradiction. 
  Qed.
  |});
  ("list_emp_no_tl", {|
  Lemma list_emp_no_tl : forall (l : list Z), forall (l1 : list Z), emp l -> ~tl l l1.
  Proof.
    intros [| x] l1 H.
    - intros [].
    - contradiction.
  Qed.
  |});
  ("list_no_emp_exists_tl", {|
  Lemma list_no_emp_exists_tl : forall (l : list Z), exists (l1 : list Z), ~emp l -> tl l l1.
  Proof.
    intros [| x xs].
    - exists nil. intros []. reflexivity.
    - exists xs. intros H. simpl. reflexivity.
  Qed.
  |});
  ("list_no_emp_exists_hd", {|
  Lemma list_no_emp_exists_hd : forall (l : list Z), exists (x : Z), ~emp l -> hd l x.
  Proof.
    intros [| x'].
    - exists 1. intros []. reflexivity.
    - exists x'. intros H. simpl. reflexivity.
  Qed.
  |});
  ("list_hd_no_emp", {|
  Lemma list_hd_no_emp : forall (l : list Z), forall (x : Z), hd l x -> ~emp l.
  Proof.
    intros [| x'] x H.
    - contradiction.
    - intros []. 
  Qed.
  |});
  ("list_tl_no_emp", {|
  Lemma list_tl_no_emp : forall (l : list Z), forall (l1 : list Z), tl l l1 -> ~emp l.
  Proof.
    intros [| x xs] l1 H.
    - contradiction.
    - intros [].
  Qed.
  |});
  ("list_len_0_emp", {|
  Lemma list_len_0_emp : forall (l : list Z), emp l -> len l 0.
  Proof.
    intros [| x] H.
    - reflexivity.
    - contradiction.
  Qed.
  |});
  ("list_emp_len_0", {|
  Lemma list_emp_len_0 : forall (l : list Z), forall (n : Z), emp l /\ len l n -> n = 0.
  Proof.
    intros [| x] n [He Hl].
    - inversion Hl. reflexivity.
    - contradiction.
  Qed.
  |});
  ("list_len_geq_0", {|
  Lemma list_len_geq_0 : forall (l : list Z), forall (n : Z), len l n -> n >= 0.
  Proof.
    intros l.
    induction l; intros n H; inversion H.
    - intuition.
    - apply IHl in H1. intuition.
  Qed. 
  |});
  ("list_positive_len_is_not_emp", {|
  Lemma list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), len l n /\ n > 0 -> ~emp l.
  Proof.
    intros [| x] n [Hl Hn].
    - inversion Hl as [Hn']. rewrite Hn' in Hn. inversion Hn.
    - intros H. contradiction.
  Qed.
  |});
  ("list_tl_len_plus_1", {|
  Lemma list_tl_len_plus_1 : forall (l : list Z), forall (l1 : list Z), forall (n : Z), tl l l1 -> len l1 n <-> len l (n + 1).
  Proof.
    intros [| x] l1 n Ht; split;
    try contradiction;
    inversion Ht; intros Hl.
    - simpl. split.
      * apply list_len_geq_0 in Hl.
        intuition.
      * replace (n + 1 - 1) with n by intuition.
        assumption.
    - simpl in Hl. destruct Hl.
      replace (n + 1 - 1) with n in H1 by intuition.
      assumption.
  Qed.
  |});
  ("list_hd_is_mem", {|
  Lemma list_hd_is_mem : forall (l : list Z), forall (u : Z), hd l u -> list_mem l u.
  Proof.
    intros [| x] u H.
    - contradiction.
    - simpl in H. simpl. left. apply H.
  Qed.
  |});
  ("list_emp_no_mem", {|
  Lemma list_emp_no_mem : forall (l : list Z), forall (u : Z), emp l -> ~list_mem l u.
  Proof.
    intros [| x] u H.
    - intros H1. contradiction.
    - contradiction.
  Qed.
  |});
  ("list_emp_unique", {|
  Lemma list_emp_unique : forall (l : list Z), emp l -> uniq l.
  Proof.
    intros [| x] H.
    - reflexivity.
    - contradiction.
  Qed.
  |});
  ("list_tl_unique", {|
  Lemma list_tl_unique : forall (l : list Z) (l1 : list Z), tl l l1 /\ uniq l -> uniq l1.
  Proof.
    intros [| x] l1 [Ht Hu].
    - contradiction.
    - simpl in Hu. destruct Hu.
      inversion Ht. assumption.
  Qed.
  |});
  ("list_hd_unique", {|
  Lemma list_hd_unique : forall (l : list Z) (l1 : list Z) (x : Z),
    tl l l1 /\ uniq l /\ hd l x -> ~ (list_mem l1 x).
  Proof.
    intros [| x] l1 x1 [Ht [Hu Hh]].
    - contradiction.
    - simpl in Hu. destruct Hu as [Htm Htu].
      inversion Hh. inversion Ht.
      assumption.
  Qed.
  |});
  ("list_hd_sorted", {|
  Lemma list_hd_sorted : forall (l : list Z) (l1 : list Z) (x : Z) (y : Z),
    tl l l1 /\ sorted l -> emp l1 \/ ((hd l1 y /\ hd l x) -> (x <= y)).
  Proof.
    intros [| x1] [| y1] x y [Htl Hs]; try contradiction.
    - left. reflexivity.
    - right. intros [Hht Hhp].
      inversion Htl. inversion Hht. inversion Hhp.
      subst. simpl in Hs. intuition.
  Qed.
  |});
  ("list_tl_sorted", {|
  Lemma list_tl_sorted : forall (l : list Z) (l1 : list Z), tl l l1 /\ sorted l -> sorted l1.
  Proof.
    intros [| x] [| y] [Ht Hs];
    try contradiction.
    - reflexivity.
    - inversion Ht. subst. simpl in Hs. destruct l0.
      * reflexivity.
      * simpl. intuition.
  Qed.
  |})
]

module StringSet = Set.Make(String)

let builtins = StringSet.of_list [
  "=="; "!="; "<"; "<="; ">"; ">="; "+"; "-"; "*"; "/"; "mod"; "True"; "False";
  "Nil"; "Cons"; "Leaf"; "Node"; "None"; "Some"; "Rbtleaf"; "Rbtnode"  (* Ignore custom constructors in proof file generation; TODO? *)
]

let remove_builtins (types : (Nt.t, string) typed list) =
  List.filter (fun { x; _ } -> not @@ StringSet.mem x builtins) types
