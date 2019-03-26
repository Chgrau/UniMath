(*
We define the presheaf category known as the topos of trees.
Topos of trees is the presheaf category over ω, the preorder of natural numbers ordered by inclusion.

In topos_of_trees we define:
  - The later endofunctor
  - The prev endofunctor
  - Show adjunction between later and prev.
*)


Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.MoreFoundations.Nat.

Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.categories.preorder_categories.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.opp_precat.

Local Open Scope cat.
Local Open Scope nat.


Section ToT_definition.

Definition inclusion_relation : hrel ℕ := λ(n m : ℕ), n ≤ m.

Lemma inclusion_relation_is_preorder : ispreorder inclusion_relation.
Proof.
  split.
  - unfold istrans.
    exact @istransnatleh.
  - unfold isrefl.
    exact @isreflnatleh.
Defined.

Definition inclusion_relation_po : po ℕ := (popair inclusion_relation inclusion_relation_is_preorder).

Definition ω  : precategory := po_precategory inclusion_relation_po.

Definition ω_succ : ω^op → ω^op := λ n, S n.

Definition topos_of_trees : category := PreShv ω.

Definition has_homsets_topos_of_trees : has_homsets topos_of_trees :=
  (functor_category_has_homsets ω^op HSET has_homsets_HSET).

End ToT_definition.

Section Later.

Lemma ω_map_succ : ∏(n m : ω^op), ω^op⟦ω_succ n, ω_succ m⟧ → ω^op⟦n, m⟧.
Proof.
  intros n m f.
  exact f.
Defined.

Definition later_on_ob_on_ob (A : topos_of_trees) :  ω^op → SET.
Proof.
  intros n.
  destruct n as [|n].
  - exact TerminalHSET.
  - exact ((pr1 A) n).
Defined.

Definition later_on_ob_on_mor (A : topos_of_trees) :
  ∏(n m : nat)(f : (ω ^op)⟦n, m⟧), HSET⟦(later_on_ob_on_ob A) n, (later_on_ob_on_ob A) m⟧.
Proof.
  intros n m f.
  destruct m as [| m].
  - apply (TerminalArrow TerminalHSET).
  - destruct n as [| n].
    + inversion f.
    + apply ω_map_succ in f.
      apply (#(pr1 A) f).
Defined.

Definition later_on_ob_data (A : topos_of_trees) : functor_data (ω ^op) SET :=
  mk_functor_data (later_on_ob_on_ob A) (later_on_ob_on_mor A).

Definition later_on_ob_idax (A : topos_of_trees) : functor_idax (later_on_ob_data A).
Proof.
  intro n.
  destruct n as [|n].
  - apply (TerminalArrowEq (TerminalArrow TerminalHSET unitHSET)).
  - apply A.
Defined.

Definition later_on_ob_compax (A : topos_of_trees) : functor_compax (later_on_ob_data A).
Proof.
  intros n m k f g.
  destruct k as [|k].
  - apply (TerminalArrowEq (TerminalArrow TerminalHSET (later_on_ob_on_ob A n))).
  - destruct m as [|m].
    + inversion g.
    + destruct n as [|n].
      * inversion f.
      * simpl. unfold compose.
        rewrite <- (functor_comp A).
        apply maponpaths.
        apply po_homsets_isaprop.
Defined.

Definition later_on_ob_is_functor (A : topos_of_trees) : is_functor (later_on_ob_data A) :=
  ((later_on_ob_idax A) ,,  (later_on_ob_compax A)).

Definition later_on_ob (A : topos_of_trees) : topos_of_trees :=
  mk_functor (later_on_ob_data A) (later_on_ob_is_functor A).

Definition later_on_mor_data (A B : topos_of_trees) (τ : topos_of_trees ⟦ A, B ⟧) :
      nat_trans_data (later_on_ob_data A) (later_on_ob_data B).
Proof.
  intros n x.
  destruct n as [|n].
  - exact tt.
  - exact (pr1 τ n x).
Defined.

Definition later_on_mor_is_nat_trans (A B : topos_of_trees) (τ : topos_of_trees ⟦ A, B ⟧) :
  is_nat_trans (later_on_ob_data A) (later_on_ob_data B) (later_on_mor_data A B τ).
Proof.
  intros n m f.
  destruct m as [|m].
  - apply idpath.
  - destruct n as [|n].
    + inversion f.
    + exact (pr2 τ n m f).
Defined.

Definition later_on_mor (A B : topos_of_trees) (τ : topos_of_trees ⟦ A, B ⟧) :
  topos_of_trees ⟦ later_on_ob A, later_on_ob B ⟧.
  use mk_nat_trans.
  - exact (later_on_mor_data A B τ).
  - exact (later_on_mor_is_nat_trans A B τ).
Defined.

Definition later_data : functor_data topos_of_trees topos_of_trees := mk_functor_data later_on_ob later_on_mor.

Definition later_idax : functor_idax later_data.
Proof.
  intro A.
  use (nat_trans_eq has_homsets_HSET).
  intro n.
  destruct n as [| n].
  - apply (@TerminalArrowEq HSET TerminalHSET unitHSET).
  - apply idpath.
Defined.

Definition later_compax : functor_compax later_data.
Proof.
  intros A B C τ σ.
  use (nat_trans_eq has_homsets_HSET).
  intro n.
  destruct n as [|n]; apply idpath.
Defined.

Definition later : functor topos_of_trees topos_of_trees := mk_functor later_data (later_idax ,, later_compax).

End Later.

Section Earlier.

Lemma ω_map_succ' : ∏(n m : ω^op), ω^op⟦n, m⟧ → ω^op⟦ω_succ n, ω_succ m⟧.
Proof.
  intros n m f.
  exact f.
Defined.

Definition succ_functor : functor ω^op ω^op.
Proof.
  use mk_functor.
  - use mk_functor_data.
    + intro n; exact (S n).
    + intros a b f. exact f.
  - split.
    + intro n.
      apply idpath.
    + intros n m k f g.
      apply po_homsets_isaprop.
Defined.

Definition earlier_on_ob (A : topos_of_trees) : topos_of_trees.
Proof.
  exact (functor_composite succ_functor A).
Defined.

Definition earlier_on_mor_data (A B : topos_of_trees) (τ : topos_of_trees ⟦ A, B ⟧) :
      nat_trans_data (pr1 (earlier_on_ob A)) (pr1 (earlier_on_ob B)).
Proof.
  intros n x.
  exact (pr1 τ (S n) x).
Defined.

Definition earlier_on_mor_is_nat_trans (A B : topos_of_trees) (τ : topos_of_trees ⟦ A, B ⟧) :
  is_nat_trans (pr1 (earlier_on_ob A)) (pr1 (earlier_on_ob B)) (earlier_on_mor_data A B τ).
Proof.
  intros n m f.
  exact (pr2 τ (S n) (S m) f).
Defined.

Definition earlier_on_mor (A B : topos_of_trees) (τ : topos_of_trees ⟦ A, B ⟧) :
  topos_of_trees ⟦ earlier_on_ob A, earlier_on_ob B ⟧.
  use mk_nat_trans.
  - exact (earlier_on_mor_data A B τ).
  - exact (earlier_on_mor_is_nat_trans A B τ).
Defined.

Definition earlier_data : functor_data topos_of_trees topos_of_trees := mk_functor_data earlier_on_ob earlier_on_mor.

Definition earlier_idax : functor_idax earlier_data.
Proof.
  intro A.
  use (nat_trans_eq has_homsets_HSET).
  intro n.
  apply idpath.
Defined.

Definition earlier_compax : functor_compax earlier_data.
Proof.
  intros A B C τ σ.
  use (nat_trans_eq has_homsets_HSET).
  intro n.
  apply idpath.
Defined.

Definition earlier : functor topos_of_trees topos_of_trees :=
  mk_functor earlier_data (earlier_idax ,, earlier_compax).

End Earlier.


Section Adjunction.

Definition compose_left_id_aux (A : topos_of_trees) :
  topos_of_trees ⟦ (functor_identity topos_of_trees) A, (earlier ∙ later) A ⟧.
Proof.
  use mk_nat_trans.
  - intros n. destruct n as [|n].
    + apply (TerminalArrow TerminalHSET).
    + apply identity.
  - intros n m f.
    destruct n as [|n].
    + destruct m as [|m].
      * apply idpath.
      * inversion f.
    + destruct m as [|m].
      * apply idpath.
      * simpl.
        unfold compose. simpl.
        apply idpath.
Defined.

Definition compose_left_id : functor_identity topos_of_trees ⟹ earlier ∙ later.
Proof.
  use mk_nat_trans.
  - intro A.
    apply (compose_left_id_aux A).
  - intros A B f.
    use (nat_trans_eq has_homsets_HSET).
    + intro n.
      destruct n as [|n]; apply idpath.
Defined.

Definition compose_right_id : later ∙ earlier ⟹ functor_identity topos_of_trees.
Proof.
  use mk_nat_trans.
  - intro A. simpl.
    use mk_nat_trans.
    + intros n X.
      exact X.
    + intros n m f.
      apply idpath.
  - intros A B f.
    use (nat_trans_eq has_homsets_HSET).
    intro n.
    apply idpath.
Defined.

Definition later_earlier_adjoint : are_adjoints earlier later.
Proof.
  use mk_are_adjoints.
  - exact compose_left_id.
  - exact compose_right_id.
  - use mk_form_adjunction.
    + intro A.
      use (nat_trans_eq has_homsets_HSET).
      intro n.
      apply idpath.
    + intro A.
      use (nat_trans_eq has_homsets_HSET).
      intro n.
      destruct n as [|n].
      * apply (@TerminalArrowEq HSET TerminalHSET unitHSET).
      * apply idpath.
Defined.

End Adjunction.

Section Fix.

Definition terminal_topos_of_trees : Terminal topos_of_trees :=
  (Terminal_functor_precat ω^op SET TerminalHSET has_homsets_HSET).

Definition terminal_map_insert (A B : topos_of_trees) (F : topos_of_trees⟦terminal_topos_of_trees,A⟧) :
  topos_of_trees⟦B,A⟧.
Proof.
  exact ((TerminalArrow terminal_topos_of_trees B)· F).
Defined.

Definition terminalHSET_eq (X : SET) (F : SET⟦TerminalHSET,X⟧) :
  TerminalArrow TerminalHSET unitHSET · F = F.
Proof.
  rewrite <- id_left.
  apply cancel_postcomposition.
  apply TerminalArrowEq.
Defined.

Definition fix_hom_data (A : topos_of_trees) (F : topos_of_trees⟦later A, A⟧) :
  ∏ n : ω^op, pr1 (TerminalObject terminal_topos_of_trees) n -->  pr1 A n.
Proof.
  induction n as [|n Hn].
  - apply (pr1 F 0).
  - apply (pr1 F (ω_succ n) ∘ Hn).
Defined.

Definition fix_hom (A : topos_of_trees) (F : topos_of_trees⟦(later A),A⟧) :
  topos_of_trees⟦terminal_topos_of_trees,A⟧.
Proof.
  use mk_nat_trans.
  - exact (fix_hom_data A F).
  - intros n m f.
    rewrite terminalHSET_eq.
    induction n as [|n Hn].
    + induction m as [|m Hm];[|inversion f].
      assert (H: f =  @identity ω^op 0);[apply po_homsets_isaprop|].
      rewrite H. rewrite functor_id.
      apply idpath.
    + induction m as [|m Hm].
      * simpl in Hn.
        simpl. rewrite (Hn f).
        unfold functor_on_morphisms in *.
        unfold compose.
        simpl.



















Definition