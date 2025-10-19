(*  BST 和 tree 的实现和性质来自 Software Foundations Volume 3
    Verified Functional Algorithms, SearchTree 一节
    https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html

    我们给出了递归合并排序二叉树的 merge 算法，并证明了其正确性 merge_correct *)
(*  本程序在 rocq 9.0.0 下编译通过 *)
From Stdlib Require Export List.
Export ListNotations.
From Stdlib Require Import FunctionalExtensionality.

Ltac inv H :=
  inversion H; subst; clear H.

Definition key := nat.

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).

Arguments E {V}.
Arguments T {V}.

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

Hint Constructors BST : core.

Fixpoint elements {V : Type} (t : tree V) : list (key * V) :=
  match t with
  | E => []
  | T l k v r => elements l ++ [(k, v)] ++ elements r
  end.

Fixpoint split_rightmost {V} (l : tree V) (k : key) (v : V) (r : tree V) : (nat * V * tree V * tree V) :=
  match r with
  | E => (k, v, E, l)
  | T l' k' v' r' =>
    match split_rightmost l' k' v' r' with
    | (k0, v0, f, s) => (k0, v0, T l k v f, s)
    end
  end.

Lemma split_correct : forall V l k (v : V) r k' v' f s,
  split_rightmost l k v r = (k', v', f, s) ->
  elements (T l k v r) = elements f ++ elements s ++ [(k', v')].
Proof.
  intros V l k v r. revert l k v.
  induction r; intros.
  - simpl in H. inversion H; subst. simpl. auto.
  - simpl in H.
    destruct (split_rightmost r1 k v r2) as [[[]]] eqn:?.
    inversion H; subst.
    simpl. rewrite <-app_assoc. simpl.
    rewrite app_inv_head_iff. f_equal.
    eauto.
Qed.

From Stdlib Require Import Lia.
From Stdlib Require Import Recdef.

Function merge {V} (t1 t2 : tree V) {measure (fun t => length (elements t)) t1} :=
  match t1 with
  | E => t2
  | T l k v r => match split_rightmost l k v r with
    | (k', v', f, s) => T (merge f s) k' v' t2
    end
  end.
Proof.
  intros.
  pose proof (split_correct _ _ _ _ _ _ _ _ _ teq0).
  rewrite H.
  rewrite length_app.
  rewrite length_app.
  simpl. lia.
Qed.

Arguments merge {V}.

Definition keys {V} (t : tree V) := map fst (elements t).

Definition merge_correct_spec := forall V (t1 t2 tm: tree V),
  BST t1 ->
  BST t2 ->
  (forall k1 k2, In k1 (keys t1) -> In k2 (keys t2) -> k1 < k2) ->
  merge t1 t2 = tm ->
  BST tm /\ elements t1 ++ elements t2 = elements tm.

Theorem merge_elements : forall V (t1 t2 : tree V),
  elements (merge t1 t2) = elements t1 ++ elements t2.
Proof.
  intros.
  apply merge_ind; intros.
  - auto.
  - simpl. rewrite H.
    pose proof (split_correct _ _ _ _ _ _ _ _ _ e0).
    simpl in H0. rewrite H0.
    repeat rewrite <-app_assoc. auto.
Qed.

Inductive ssorted : list nat -> Prop :=
| ssorted_nil : ssorted []
| ssorted_1 : forall x, ssorted [x]
| ssorted_cons : forall x y l, x < y -> ssorted (y :: l) -> ssorted (x :: y :: l).

Lemma ssorted_cons1 : forall a l, ssorted l -> Forall (lt a) l -> ssorted (a :: l).
Proof.
  intros.
  destruct l; constructor; auto.
  inv H0; auto.
Qed.

Lemma ssorted_cons1_inv : forall a l, ssorted (a :: l) -> ssorted l /\ Forall (lt a) l.
Proof.
  induction l; intros.
  - split; constructor.
  - inv H. split; auto.
    constructor; auto.
    apply IHl.
    destruct l; constructor.
    all: inv H4; try lia; auto.
Qed.

Theorem ssorted_app : forall (l1 l2 : list nat),
  ssorted l1 ->
  ssorted l2 ->
  (forall n1 n2, In n1 l1 -> In n2 l2 -> n1 < n2) ->
  ssorted (l1 ++ l2).
Proof.
  induction l1; intros; auto.
  simpl.
  destruct l1.
  - simpl. destruct l2.
    + constructor.
    + constructor; auto. apply H1; constructor; auto.
  - simpl. constructor.
    + inv H. auto.
    + apply IHl1; auto.
      * inv H; auto.
      * intros. apply H1; auto.
        right. auto.
Qed.

Theorem ssorted_app_inv : forall l1 l2,
  ssorted (l1 ++ l2) ->
  ssorted l1 /\ ssorted l2 /\ (forall n1 n2, In n1 l1 -> In n2 l2 -> n1 < n2).
Proof.
  induction l1; intros; simpl in H.
  - split; try constructor; auto.
    intros. inv H0.
  - apply ssorted_cons1_inv in H.
    destruct H.
    destruct (IHl1 _ H) as [? [? ?]].
    rewrite Forall_app in H0.
    intuition. apply ssorted_cons1; auto.
    destruct H0.
    + subst. rewrite Forall_forall in H5. auto.
    + auto.
Qed.

Lemma ForallT_Forall_iff : forall V (t : tree V) (P : key -> V -> Prop),
  ForallT P t <-> Forall (fun '(k, v) => P k v) (elements t).
Proof with auto.
  induction t; intros.
  - simpl. split...
  - simpl. split; intros.
    + destruct H as [? []].
      apply Forall_app. split.
      * apply IHt1...
      * constructor... apply IHt2...
    + apply Forall_app in H. destruct H.
      inv H0. repeat split...
      * apply IHt1...
      * apply IHt2...
Qed.

Ltac rewrite_forall := match goal with
  | H: Forall ?P1 ?l |- Forall ?P2 ?l => replace P2 with P1; auto
  end.

Theorem bst_ssorted : forall {V} (t : tree V), BST t -> ssorted (keys t).
Proof.
  unfold keys.
  intros.
  induction H; simpl; try constructor.
  apply ForallT_Forall_iff in H, H0.
  rewrite map_app. simpl.
  apply ssorted_app; auto.
  + apply ssorted_cons1; auto.
    apply Forall_map.
    rewrite_forall.
    extensionality u.
    destruct u. auto.
  + intros.
    rewrite Forall_forall in H, H0.
    rewrite in_map_iff in H3.
    destruct H3 as [x1 [? ?]].
    specialize (H _ H5). destruct x1. simpl in H3. subst.
    inv H4; auto.
    rewrite in_map_iff in H3. destruct H3 as [x2 [? ?]].
    specialize (H0 _ H4). destruct x2. simpl in H3. subst. lia.
Qed.


Theorem ssorted_bst : forall {V} (t : tree V), ssorted (keys t) -> BST t.
Proof. unfold keys.
  induction t; intros; auto.
  simpl in H. rewrite map_app in H. simpl in H.
  destruct (ssorted_app_inv _ _ H) as [? [? ?]].
  apply ssorted_cons1_inv in H1. destruct H1. intuition.
  constructor; auto; apply ForallT_Forall_iff.
  - apply Forall_forall. intros. destruct x.
    apply H2.
    + apply in_map_iff. exists (k0, v0). auto.
    + left. auto.
  - rewrite Forall_map in H3. rewrite_forall. extensionality u. destruct u. auto.
Qed.

Theorem merge_bst : forall V (t1 t2 tm : tree V),
  BST t1 -> BST t2 ->
  (forall k1 k2, In k1 (keys t1) -> In k2 (keys t2) -> k1 < k2) ->
  BST (merge t1 t2).
Proof.
  intros. apply ssorted_bst. unfold keys.
  rewrite merge_elements.
  rewrite map_app.
  apply bst_ssorted in H, H0.
  apply ssorted_app; auto.
Qed.

(* Finally we prove merge_correct_spec *)
Theorem merge_correct : merge_correct_spec.
Proof.
  unfold merge_correct_spec.
  intros; subst.
  eauto using merge_bst, merge_elements.
Qed.