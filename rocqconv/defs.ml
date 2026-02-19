let built_in_defs = Hashtbl.of_seq @@ List.to_seq [
  ("hd", {|
  Definition hd {a : Type} (l : list a) (n : a) : Prop :=
    match l with
    | nil => False
    | cons n' _ => n = n'
    end.
  |});
  ("len", {|
  Fixpoint len {a : Type} (l : list a) (n : Z) : Prop :=
    match l with
    | nil => n = 0
    | cons _ xs => len xs (n - 1)
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
  |})
]

let built_in_proofs = Hashtbl.of_seq @@ List.to_seq [
  ("list_emp_no_hd", {|
  Lemma list_emp_no_hd : forall (l : list Z), forall (x : Z), emp l -> ~hd l x.
  Proof.
    intros [| x'] x H.
    - intros H1. contradiction.
    - contradiction. 
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
    - intros H2. contradiction. 
  Qed.
  |});
  ("list_len_0_emp", {|
  Lemma list_len_0_emp : forall (l : list Z), emp l -> len l 0.
  Proof.
    intros [| x] H.
    - simpl. reflexivity.
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
  ("list_positive_len_is_not_emp", {|
  Lemma list_positive_len_is_not_emp : forall (l : list Z), forall (n : Z), len l n /\ n > 0 -> ~emp l.
  Proof.
    intros [| x] n [Hl Hn].
    - inversion Hl as [Hn']. rewrite Hn' in Hn. inversion Hn.
    - intros H. contradiction.
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
  |})
]
