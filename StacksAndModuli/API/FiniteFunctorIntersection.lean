module

public import StacksAndModuli.API.FlatteningIntersection

/-!
# Finite intersections of representable subfunctors

`API/FlatteningIntersection.lean` constructs the intersection object of a finite family of
objects over a scheme and proves that its structure map is an immersion when every member of
the family is.  The projective flattening argument also needs the matching representability
statement, in the universe in which the Quot and Grassmannian functors live.

This file supplies that categorical layer.  A finite conjunction of subsingleton-valued
representable functors is represented by the iterated fibre product `Scheme.interOverFin`.
The subsingleton hypothesis is exactly the hypothesis satisfied by flattening conditions; it
also makes all coherence equations of the conjunction formal rather than mathematical.

Main declarations:

* `AlgebraicGeometry.Scheme.prodFunctorLarge`;
* `AlgebraicGeometry.Scheme.interOverRepresentableByLarge`;
* `AlgebraicGeometry.Scheme.finProdFunctorLarge`;
* `AlgebraicGeometry.Scheme.finProdRepresentableByLarge`.
* `AlgebraicGeometry.Scheme.Modules.FiniteFlatRankPresentation` and its representative.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The pointwise product of two presheaves in the universe used by the Quot functor. -/
def prodFunctorLarge (F G : (Over X)ᵒᵖ ⥤ Type (u + 1)) : (Over X)ᵒᵖ ⥤ Type (u + 1) where
  obj T := F.obj T × G.obj T
  map φ := ↾fun p => (F.map φ p.1, G.map φ p.2)
  map_id T := by ext p <;> simp
  map_comp φ ψ := by ext p <;> simp

/-- The intersection represents the conjunction, in the universe used by Quot. -/
def interOverRepresentableByLarge {F G : (Over X)ᵒᵖ ⥤ Type (u + 1)} {A B : Over X}
    (hF : F.RepresentableBy A) (hG : G.RepresentableBy B)
    (hFs : ∀ T, Subsingleton (F.obj T)) (hGs : ∀ T, Subsingleton (G.obj T))
    [Mono A.hom] [Mono B.hom] :
    (prodFunctorLarge F G).RepresentableBy (interOver A B) where
  homEquiv {T} := by
    haveI := hFs (op T)
    haveI := hGs (op T)
    haveI : Mono (interOver A B).hom := interOver_mono A B
    refine Equiv.ofBijective (fun f =>
      (hF.homEquiv (Over.homMk (f.left ≫ Limits.pullback.fst _ _)
          (by rw [Category.assoc]; exact Over.w f) : T ⟶ A),
       hG.homEquiv (Over.homMk (f.left ≫ Limits.pullback.snd _ _)
          (by rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc]
              exact Over.w f) : T ⟶ B))) ?_
    constructor
    · intro a b _
      apply Over.OverMorphism.ext
      rw [← cancel_mono (interOver A B).hom, Over.w, Over.w]
    · rintro ⟨x, y⟩
      refine ⟨Over.homMk (Limits.pullback.lift (hF.homEquiv.symm x).left
        (hG.homEquiv.symm y).left (by rw [Over.w, Over.w])) ?_, ?_⟩
      · change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ ≫ _ = T.hom
        rw [← Category.assoc, Limits.pullback.lift_fst, Over.w]
      · exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  homEquiv_comp {T T'} g f := by
    haveI := hFs (op T')
    haveI := hGs (op T')
    exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- The finite conjunction of a family of presheaves.  The zero-fold conjunction is the
terminal representable presheaf, matching `interOverFin` at zero. -/
def finProdFunctorLarge : ∀ {k : ℕ}, (Fin k → (Over X)ᵒᵖ ⥤ Type (u + 1)) →
    (Over X)ᵒᵖ ⥤ Type (u + 1)
  | 0, _ => uliftYoneda.{u + 1}.obj (Over.mk (𝟙 X))
  | (_ + 1), F => prodFunctorLarge (F 0) (finProdFunctorLarge (fun i => F i.succ))

/-- A finite conjunction of subsingleton-valued functors is subsingleton-valued. -/
theorem finProdFunctorLarge_subsingleton :
    ∀ {k : ℕ} (F : Fin k → (Over X)ᵒᵖ ⥤ Type (u + 1)),
      (∀ i T, Subsingleton ((F i).obj T)) →
      ∀ T, Subsingleton ((finProdFunctorLarge F).obj T)
  | 0, _, _, T => by
      change Subsingleton (ULift ((unop T) ⟶ Over.mk (𝟙 X)))
      refine ⟨fun a b => ?_⟩
      apply ULift.ext
      apply Over.OverMorphism.ext
      simpa using (Over.w a.down).trans (Over.w b.down).symm
  | (_ + 1), F, h, T => by
      change Subsingleton ((F 0).obj T ×
        (finProdFunctorLarge (fun i => F i.succ)).obj T)
      haveI := h 0 T
      haveI := finProdFunctorLarge_subsingleton (fun i => F i.succ)
        (fun i T' => h i.succ T') T
      infer_instance

/-- A one-fold finite conjunction of a subsingleton-valued functor is canonically the
functor itself. -/
noncomputable def finProdFunctorLargeSingletonIso
    (F : (Over X)ᵒᵖ ⥤ Type (u + 1))
    (hF : ∀ A, Subsingleton (F.obj A)) :
    finProdFunctorLarge (fun _ : Fin 1 ↦ F) ≅ F where
  hom :=
    { app := fun _ ↦ ↾fun x ↦ x.1
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (hF B).elim _ _ }
  inv :=
    { app := fun A ↦ ↾fun x ↦
        (x, ULift.up
          (Over.homMk A.unop.hom (by simp) : A.unop ⟶ Over.mk (𝟙 X)))
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        haveI := finProdFunctorLarge_subsingleton
          (fun _ : Fin 1 ↦ F) (fun _ A' ↦ hF A') B
        exact Subsingleton.elim _ _ }
  hom_inv_id := by
    ext A x
    haveI := finProdFunctorLarge_subsingleton
      (fun _ : Fin 1 ↦ F) (fun _ A' ↦ hF A') A
    exact Subsingleton.elim _ _
  inv_hom_id := by
    ext A x
    exact (hF A).elim _ _

/-- A finite conjunction of representable subsingleton-valued functors is represented by the
iterated fibre product of their representatives. -/
def finProdRepresentableByLarge :
    ∀ {k : ℕ} (F : Fin k → (Over X)ᵒᵖ ⥤ Type (u + 1)) (A : Fin k → Over X),
      (∀ i, (F i).RepresentableBy (A i)) →
      (∀ i T, Subsingleton ((F i).obj T)) →
      (∀ i, Mono (A i).hom) →
      (finProdFunctorLarge F).RepresentableBy (interOverFin A)
  | 0, _, _, _, _, _ =>
      (Functor.RepresentableBy.equivUliftYonedaIso
        (uliftYoneda.{u + 1}.obj (Over.mk (𝟙 X))) (Over.mk (𝟙 X))).symm (Iso.refl _)
  | (_ + 1), F, A, hrepr, hsub, hmono => by
      haveI : Mono (A 0).hom := hmono 0
      haveI : Mono (interOverFin (fun i => A i.succ)).hom :=
        interOverFin_mono (fun i => A i.succ) (fun i => hmono i.succ)
      exact interOverRepresentableByLarge (hrepr 0)
        (finProdRepresentableByLarge (fun i => F i.succ) (fun i => A i.succ)
          (fun i => hrepr i.succ) (fun i T => hsub i.succ T) (fun i => hmono i.succ))
        (hsub 0)
        (finProdFunctorLarge_subsingleton (fun i => F i.succ)
          (fun i T => hsub i.succ T))

namespace Modules

/-- A presentation of a subsingleton moduli condition by finitely many flattening
conditions for finite quasicoherent sheaves on the base.

The substantive input in an application is `iso`: it says that the desired condition is
equivalent, compatibly with pullback, to local flatness of the listed sheaves in the listed
ranks.  Once that comparison is known, representability by an immersion is formal. -/
structure FiniteFlatRankPresentation (H : (Over X)ᵒᵖ ⥤ Type (u + 1)) where
  /-- Number of flattening conditions. -/
  count : ℕ
  /-- The finite quasicoherent sheaves whose flattening strata are intersected. -/
  sheaf : Fin count → X.Modules
  /-- The desired rank of each sheaf. -/
  rank : Fin count → ℕ
  /-- Quasicoherence of the sheaves. -/
  isQuasicoherent : ∀ i, (sheaf i).IsQuasicoherent
  /-- Finiteness on every affine open, in the form consumed by the general-base
  flattening theorem. -/
  finite : ∀ (i) (U : X.affineOpens),
    haveI : IsAffine U.1.toScheme := U.2
    Module.Finite ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Scheme.Modules.pullback U.1.ι).obj (sheaf i), ⊤)
  /-- Identification of the moduli condition with the finite conjunction of flattening
  conditions. -/
  iso : finProdFunctorLarge (fun i =>
      flatRankFunctorOver (sheaf i) (rank i) ⋙ uliftFunctor.{u + 1}) ≅ H

namespace FiniteFlatRankPresentation

variable {H : (Over X)ᵒᵖ ⥤ Type (u + 1)}

/-- The iterated fibre product of the flattening strata in a finite-flat-rank
presentation. -/
def representative (D : FiniteFlatRankPresentation H) : Over X :=
  interOverFin (fun i => @flatRankRepresentativeOfFinite X (D.sheaf i)
    (D.isQuasicoherent i) (D.rank i) (D.finite i))

/-- A finite-flat-rank presentation represents the desired moduli condition. -/
def representableBy (D : FiniteFlatRankPresentation H) :
    H.RepresentableBy D.representative := by
  let A : Fin D.count → Over X := fun i =>
    @flatRankRepresentativeOfFinite X (D.sheaf i)
      (D.isQuasicoherent i) (D.rank i) (D.finite i)
  let F : Fin D.count → (Over X)ᵒᵖ ⥤ Type (u + 1) := fun i =>
    flatRankFunctorOver (D.sheaf i) (D.rank i) ⋙ uliftFunctor.{u + 1}
  have hrepr : ∀ i, (F i).RepresentableBy (A i) := fun i =>
    (Functor.representableByUliftFunctorEquiv.{u + 1}).symm
      (@flatRankRepresentableByOfFinite X (D.sheaf i)
        (D.isQuasicoherent i) (D.rank i) (D.finite i))
  have hsub : ∀ i T, Subsingleton ((F i).obj T) := by
    intro i T
    change Subsingleton (ULift ((flatRankFunctorOver (D.sheaf i) (D.rank i)).obj T))
    haveI := Scheme.factorsFunctor_subsingleton
      (affineStratum (D.sheaf i) (D.rank i)) T
    infer_instance
  have hmono : ∀ i, Mono (A i).hom := by
    intro i
    have hi := @flatRankRepresentativeOfFinite_hom_isImmersion X (D.sheaf i)
      (D.isQuasicoherent i) (D.rank i) (D.finite i)
    haveI : IsImmersion (A i).hom := hi
    infer_instance
  exact (finProdRepresentableByLarge F A hrepr hsub hmono).ofIso D.iso

/-- The representative supplied by a finite-flat-rank presentation is immersed in the
base. -/
theorem representative_hom_isImmersion (D : FiniteFlatRankPresentation H) :
    IsImmersion D.representative.hom := by
  apply interOverFin_isImmersion
  intro i
  exact @flatRankRepresentativeOfFinite_hom_isImmersion X (D.sheaf i)
    (D.isQuasicoherent i) (D.rank i) (D.finite i)

end FiniteFlatRankPresentation

end Modules

end AlgebraicGeometry.Scheme

end
