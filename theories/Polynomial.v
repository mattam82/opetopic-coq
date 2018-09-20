From Equations Require Import Equations.
From Opetopic Require Import HoTT_light.
Import Id_Notations.
Import Sigma_Notations.
Set Universe Polymorphism.
(*Equations Logic Type Id Id_rect Id_rect_r Id_rect_dep_r Empty unit tt prod pair.*)
Set Equations Transparent.
Notation Σ i j := (sigma i j).

Record Poly@{i} (I : Type@{i}) :=
  { Op : I -> Type@{i};
    Param : forall {i : I}, Op i -> I -> Type@{i} }.
Arguments Op {I}.
Arguments Param {I} _ {i} _ _.

(* Total space of the constructors/operations, indexed by their input type *)
Definition Ops {I : Type} (P : Poly I) := sigma I (Op P).

(* Total space of the parameters/inputs of a given operation/constructor *)
Definition Arity {I} (P : Poly I) {i} (f : Op P i) := sigma I (Param P f).

(* Functions that decorate every parameter of a constructor *)
Definition Decor@{i} {I : Type@{i}} (P : Poly I) (X : I -> Type@{i}) {i} (f : Op P i) :=
  forall j, Param P f j -> X j.

(* Type of polynomials decorated with X *)
Definition decor@{i} {I : Type@{i}} (P : Poly I) (X : I -> Type@{i}) : I -> Type@{i} :=
  fun i => Σ (Op P i) (Decor P X).

(** Just use standard tuple notation for sigmas *)
Notation "( x , .. , y , z )" :=
  (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
    (right associativity, at level 0,
     format "( x ,  .. ,  y  ,  z )").

Section Trees.
  Universe i.
  Context {I : Type@{i}} (P : Poly I).

  Inductive W : I -> Type@{i} :=
  | lf (i : I) : W i
  | nd {i : I} (d : Σ (Op P i) (fun f => forall j, Param P f j -> W j)) : W i.

  Derive Signature for W.
  (* Derive NoConfusion for W. *)

  (* Leaf w j represents the type of paths to leaves of the tree with index j. *)
  Fixpoint Leaf {i} (w : W i) (j : I) :=
    match w with
    | lf k => k = j
    | nd &(f & ϕ) => Σ I (fun k => Σ (Param P f k) (fun p => Leaf (ϕ k p) j))
    end.

  (* Leaf w j represents the type of paths to nodes labelled with o. *)
  Program Fixpoint Node {i} (w : W i) (o : Ops P) : Type :=
    match w with
    | lf k => Empty
    | nd &(f & ϕ) =>
      (o = &(i & f)) +
      (Σ I (fun k => Σ (Param P f k) (fun p => Node (ϕ k p) o)))
    end.

  (* A frame for a tree [w] and operation [f] is an equivalence between
     paths to leaves in [w] indexed by [j] to parameters of [f] of the same index. *)
  Definition Frame {i} (w : W i) (f : Op P i) :=
    forall j, Leaf w j <~> Param P f j.

  Definition Relator : Type :=
    forall (i : I) (w : W i) (f : Op P i), Frame w f → Type.

  (* A corrola for [f] is a tree with a single node labelled with [f] whose
     parameters are all leaves. *)

  Definition corrola {i} (f : Op P i) : W i :=
    nd (f, fun j p => lf j).

  Equations corrola_leaf_param {i} (f : Op P i) j (l : Leaf (corrola f) j) : Param P f j :=
  corrola_leaf_param f _ (sigmaI _ (sigmaI p id_refl)) := p.

  Equations corrola_param_leaf {i} (f : Op P i) j (p : Param P f j) : Leaf (corrola f) j :=
  corrola_param_leaf f j p := (j, p, id_refl).

  Program Definition corrola_leaf_equiv {i} (f : Op P i) j :
    Leaf (corrola f) j <~> Param P f j :=
    @BuildEquiv _ _ (corrola_leaf_param f j)
                (@BuildIsEquiv _ _ _ (corrola_param_leaf f j)
                               (fun _ => id_refl) _ _).

  Next Obligation.
    intros [k [p d]]. unfold corrola_param_leaf, corrola_leaf_param.
    destruct d. exact id_refl.
  Defined.

  Next Obligation.
    destruct x as [k [p d]]. destruct d. unfold corrola_param_leaf, corrola_leaf_param.
    simpl. exact id_refl.
  Defined.

  Notation idp := id_refl.

  Equations graft {i : I} (w : W i) (ψ : ∀ j, Leaf w j → W j) : W i :=
  graft (lf i) ψ := ψ i idp ;
  graft (nd (sigmaI f ϕ)) ψ := nd &(f & λ j p, graft (ϕ j p) (λ k l, ψ k &(j , p & l))).

  Equations graft_leaf_in {i : I} (w : W i) (ψ : ∀ j, Leaf w j → W j)
      (j : I) (k : I) (l : Leaf w k) (m : Leaf (ψ k l) j) : Leaf (graft w ψ) j :=
  graft_leaf_in (lf i) ψ j ?(i) id_refl m := m;
  graft_leaf_in (nd (sigmaI f ϕ)) ψ j k (sigmaI h (sigmaI p l)) m :=
      sigmaI _ h (sigmaI _ p (graft_leaf_in (ϕ h p) (λ k₁ l₁, ψ k₁ &(h , p & l₁)) j k l m)).

  
  Equations(noeqns noind) graft_leaf_elim {i : I} (w : W i)
        (ψ : ∀ j, Leaf w j → W j)  (j : I) (Q : forall (l : Leaf (graft w ψ) j), Type)
        (σ : forall (k : I) (l : Leaf w k) (m : Leaf (ψ k l) j), Q (graft_leaf_in w ψ j k l m))
        (l : Leaf (graft w ψ) j) : Q l :=
  graft_leaf_elim (lf i) ψ j Q σ l := σ i id_refl l;
  graft_leaf_elim (nd (sigmaI f ϕ)) ψ j Q σ (sigmaI h (sigmaI p l)) :=
    graft_leaf_elim (ϕ h p) (λ j₁ l₁, ψ j₁ &(h , p & l₁)) j
                    (λ l₁, Q &(h , p & l₁)) (λ k₁ l₁ m₁, σ k₁ &(h , p & l₁) m₁) l.

  Lemma graft_leaf_elim_β {i : I} (w : W i)
        (ψ : ∀ j, Leaf w j → W j)  (j : I) (Q : forall (l : Leaf (graft w ψ) j), Type)
        (σ : forall (k : I) (l : Leaf w k) (m : Leaf (ψ k l) j), Q (graft_leaf_in w ψ j k l m))
        (k : I) (l : Leaf w k) (m : Leaf (ψ k l) j) :
    graft_leaf_elim w ψ j Q σ (graft_leaf_in w ψ j k l m) = σ k l m.
  Proof.
    revert_until i. revert i. fix aux 2.
    intros i w. destruct w. intros.
    simpl. destruct l. constructor.
    intros. simpl. destruct d as [op phi]; simpl in l. destruct l as [h [p l]].
    apply (aux _ (phi h p) (λ j₁ l₁, ψ j₁ (h , p, l₁))
                    _ (λ l₁, Q (h , p, l₁)) (λ k₁ l₁ m₁, σ k₁ (h, p, l₁) m₁) k l m).
  Defined.

  Equations graft_leaf_rec {i : I} (w : W i)
        (ψ : ∀ j, Leaf w j → W j)  (j : I) (Q : Type)
        (σ : forall (k : I) (l : Leaf w k) (m : Leaf (ψ k l) j), Q)
        (l : Leaf (graft w ψ) j) : Q :=
  graft_leaf_rec (lf i) ψ j Q σ l := σ i id_refl l;
  graft_leaf_rec (nd (sigmaI f ϕ)) ψ j Q σ (sigmaI h (sigmaI p l)) :=
    graft_leaf_rec (ϕ h p) (λ j₁ l₁, ψ j₁ (h, p, l₁)) j
                    Q (λ k₁ l₁ m₁, σ k₁ (h, p, l₁) m₁) l.

  Lemma graft_leaf_rec_β {i : I} (w : W i)
        (ψ : ∀ j, Leaf w j → W j)  (j : I) (Q : Type)
        (σ : forall (k : I) (l : Leaf w k) (m : Leaf (ψ k l) j), Q)
        (k : I) (l : Leaf w k) (m : Leaf (ψ k l) j) :
    graft_leaf_rec w ψ j Q σ (graft_leaf_in w ψ j k l m) = σ k l m.
  Proof.
    revert_until i. revert i. fix aux 2.
    intros i w. destruct w. intros.
    simpl. destruct l. constructor.
    intros. simpl. destruct d as [op phi]; simpl in l. destruct l as [h [p l]].
    apply (aux _ (phi h p) (λ j₁ l₁, ψ j₁ (h , p, l₁))
                    _ Q (λ k₁ l₁ m₁, σ k₁ (h , p, l₁) m₁) k l m).
  Defined.

  Lemma graft_unit {i : I} (w : W i) : graft w (λ j l, lf j) = w.
  Proof.
    revert i w. fix aux 2.
    destruct w; intros.
    simpl. reflexivity.
    destruct d as [f ϕ]. simpl.
    apply ap. apply ap.
    apply path_forall. intros x.
    apply path_forall. intros p.
    apply aux.
  Defined.

  Lemma graft_assoc {i : I} (w : W i)
      (ψ₀ : ∀ j, Leaf w j → W j)
      (ψ₁ : ∀ j k (l : Leaf w k), Leaf (ψ₀ k l) j → W j) :
    graft (graft w ψ₀) (λ j, graft_leaf_rec w ψ₀ j _ (ψ₁ j))
    = graft w (λ j l, graft (ψ₀ j l) (λ k m, ψ₁ k j l m)).
  Proof.
    revert i w ψ₀ ψ₁.
    fix aux 2.
    destruct w; intros.
    simpl. reflexivity.
    destruct d as [f ϕ]. simpl.
    apply ap. apply ap.
    apply path_forall. intros x.
    apply path_forall. intros p.
    apply aux.
  Defined.
*)

  Definition slice (R : Relator) : Poly (Σ I (Op P)) :=
    {| Op '(i, f) := Σ (W i) (λ w, Σ (Frame w f) (R _ w f)) ;
       Param i w g := Node w.1 g |}.

End Trees.

Infix "/" := (slice).

CoInductive PolyDomain (I : Type) (P : Poly I) :=
  { R : Relator P;
    Dm : PolyDomain _ (P / R) }.

Section Substitution.
  Context {I : Type} (P : Poly I) (R : Relator P).


Equations substitute {i : I} (w : W P i) (k : forall (jc : Σ I (Op P)), Node P w jc -> W (P / R) jc) : W P i :=
{ substitute (lf i) κ := lf _ i ;
  substitute (nd i  (sigmaI f ϕ)) κ :=
                           (let pd := κ (i , f) (inl id_refl) in
                           let _ := flatten _ _ pd in _)
(*    let p j l := flatten_frm_to pd j l in
    let ε j l := substitute (ϕ j (p j l)) (fun ic n => κ ic (inr (j , p j l , n))) in
    graft P (flatten pd) ε *)
where
flatten (i : I) (f : Op P i) (pd : W (P / R) (i , f)) : W P i := 
flatten i f (lf _) := corrola P f;
flatten i f (nd (sigmaI (sigmaI w (sigmaI α r)) κ)) := substitute w κ }.

where
flatten_frm_to {i : I} {f : Op P i}  (pd : W (P / R) (i , f)) (j : I)  (l : Leaf P (flatten pd) j) : Param P f j :=
flatten_frm_to (lf _) j (sigmaI _ (sigmaI p idp)) := p;
flatten_frm_to (nd (sigmaI (sigmaI w (sigmaI α r)) κ)) j l := f (α j) (substitute-lf-to w κ j l)
where
substitute_lf_to {i : I} (w : W P i) (κ : (c : Σ I (Op P)) → Node P w c → W (P // R) c) (j : I) (l : Leaf P (substitute w κ) j) : Leaf P w j :=
substitute_lf_to (lf i) κ j l := l ;
substitute_lf_to (nd i (sigmaI f ϕ)) κ j l := 
    let pd := κ (i , f) (inl idp) in
    let p j l := flatten-frm-to pd j l in
    let κ' j l ic n := κ ic (inr (j , p j l , n)) in
    let ε j l := substitute (ϕ j (p j l)) (fun ic n =>  κ ic (inr (j , p j l , n))) in
    let (k , l₀ , l₁) := graft-leaf-from P (flatten pd) ε j l in
    let p' := flatten-frm-to pd k l₀ in
    let l' := substitute-lf-to (ϕ k (p k l₀)) (κ' k l₀) j l₁
    in (k , p' , l')
.

