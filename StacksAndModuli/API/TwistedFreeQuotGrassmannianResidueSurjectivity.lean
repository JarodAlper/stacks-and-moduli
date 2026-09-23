module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNatTrans
public import StacksAndModuli.API.AffineQuasicoherentResidueSurjectivity

/-!
# Residue-fibre detection for the Quot-to-Grassmannian free map

This file connects the affine Nakayama criterion to the finite-free section map used in
the Quot-to-Grassmannian construction.  It is independent of the projective regularity
argument: once the normalized free map is surjective after every residue-field pullback,
finite local freeness of its target upgrades it to surjectivity on every affine open.

Main declarations:
- `Scheme.Modules.finFreeSectionsMap'_surjective_of_app_surjective`;
- `Scheme.Modules.finFreeSectionsMap'_surjective_of_coordinate_residue_pullbacks_of_rank`.
- `Scheme.Modules.affineOpenResiduePullbackIso`.
- `Scheme.Modules.epi_of_geometric_residue_pullbacks_of_rank`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The geometric pullback from an affine open to one of its quotient-ring fibres agrees
functorially with first restricting to the open, transporting it to its canonical
spectrum, and then pulling back along the quotient map. -/
noncomputable def affineOpenResiduePullbackFunctorIso
    {X : Scheme.{u}} (U : X.affineOpens) (I : Ideal Γ(X, U.1)) :
    let i := U.1.ι
    let j := U.2.isoSpec.inv
    let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    restrictFunctor i ⋙ restrictFunctor j ⋙ pullback k ≅
      pullback (k ≫ (j ≫ i)) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (restrictFunctor U.1.ι)
        (restrictFunctorIsoPullback U.2.isoSpec.inv))
      (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (restrictFunctorIsoPullback U.1.ι)
        (pullback U.2.isoSpec.inv))
      (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≪≫
    Functor.isoWhiskerRight (pullbackComp U.2.isoSpec.inv U.1.ι)
      (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≪≫
    pullbackComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (U.2.isoSpec.inv ≫ U.1.ι)

/-- Object component of `affineOpenResiduePullbackFunctorIso`. -/
noncomputable def affineOpenResiduePullbackIso
    {X : Scheme.{u}} (U : X.affineOpens) (I : Ideal Γ(X, U.1))
    (M : X.Modules) :
    let i := U.1.ι
    let j := U.2.isoSpec.inv
    let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    (pullback k).obj ((restrictFunctor j).obj ((restrictFunctor i).obj M)) ≅
      (pullback (k ≫ (j ≫ i))).obj M :=
  (affineOpenResiduePullbackFunctorIso U I).app M

/-- Naturality of `affineOpenResiduePullbackIso` in the module sheaf. -/
lemma affineOpenResiduePullbackIso_naturality
    {X : Scheme.{u}} (U : X.affineOpens) (I : Ideal Γ(X, U.1))
    {M N : X.Modules} (p : M ⟶ N) :
    let i := U.1.ι
    let j := U.2.isoSpec.inv
    let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let pU := (restrictFunctor j).map ((restrictFunctor i).map p)
    (pullback k).map pU ≫ (affineOpenResiduePullbackIso U I N).hom =
      (affineOpenResiduePullbackIso U I M).hom ≫
        (pullback (k ≫ (j ≫ i))).map p := by
  exact (affineOpenResiduePullbackFunctorIso U I).hom.naturality p

/-- A quasicoherent morphism with finite-locally-free target is an epimorphism if its
pullback to every closed residue fibre of every affine chart is surjective on global
sections.  The fibre map is stated geometrically, along the composite map to the original
scheme; `affineOpenResiduePullbackIso` supplies the coordinate normalization required by
affine Nakayama. -/
theorem epi_of_geometric_residue_pullbacks_of_rank
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {q : ℕ}
    (p : M ⟶ N) (hN : IsProjectiveOfRank q N)
    (h : ∀ (U : X.affineOpens) (I : Ideal Γ(X, U.1)), I.IsMaximal →
      let i := U.1.ι
      let j := U.2.isoSpec.inv
      let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      Function.Surjective
        (Hom.app ((pullback (k ≫ (j ≫ i))).map p) ⊤)) :
    Epi p := by
  apply epi_of_coordinate_residue_pullbacks_of_rank p hN
  intro U I hI
  let i := U.1.ι
  let j := U.2.isoSpec.inv
  let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let pU := (restrictFunctor j).map ((restrictFunctor i).map p)
  have hpull : Function.Surjective
      (Hom.app ((pullback (k ≫ (j ≫ i))).map p) ⊤) := h U I hI
  exact surjective_app_of_arrow_iso
    ((pullback k).map pU) ((pullback (k ≫ (j ≫ i))).map p)
    (affineOpenResiduePullbackIso U I M)
    (affineOpenResiduePullbackIso U I N)
    (affineOpenResiduePullbackIso_naturality U I p) ⊤ hpull

/-- Categorical form of `epi_of_geometric_residue_pullbacks_of_rank`: it is enough that
every geometric closed-residue pullback of the morphism is an epimorphism. -/
theorem epi_of_geometric_residue_pullbacks_epi_of_rank
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {q : ℕ}
    (p : M ⟶ N) (hN : IsProjectiveOfRank q N)
    (h : ∀ (U : X.affineOpens) (I : Ideal Γ(X, U.1)), I.IsMaximal →
      let i := U.1.ι
      let j := U.2.isoSpec.inv
      let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      Epi ((pullback (k ≫ (j ≫ i))).map p)) :
    Epi p := by
  apply epi_of_geometric_residue_pullbacks_of_rank p hN
  intro U I hI
  let i := U.1.ι
  let j := U.2.isoSpec.inv
  let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let s := k ≫ (j ≫ i)
  let pI := (pullback s).map p
  letI : Epi pI := h U I hI
  exact (epi_iff_appTop_surjective pI).mp inferInstance

/-- Surjectivity of the actual section map out of a finite free sheaf implies
surjectivity of its generator-coordinate form. -/
lemma finFreeSectionsMap'_surjective_of_app_surjective
    {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (p : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (U : X.Opens) (h : Function.Surjective (Hom.app p U)) :
    Function.Surjective (finFreeSectionsMap' p U) := by
  rw [← finFreeSectionsMap_eq_finFreeSectionsMap' p U]
  exact h.comp ((freeSectionsEquiv U).symm.surjective.comp
    (LinearEquiv.funCongrLeft Γ(X, U) Γ(X, U)
      (Equiv.ulift.{u, 0} (α := Fin m))).surjective)

/-- A finite-free map into a fixed-rank quasicoherent sheaf is surjective on an affine
open once its coordinate transport to every closed residue fibre is surjective. -/
theorem finFreeSectionsMap'_surjective_of_coordinate_residue_pullbacks_of_rank
    {X : Scheme.{u}} {m q : ℕ} {M : X.Modules} [M.IsQuasicoherent]
    (p : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (hM : IsProjectiveOfRank q M) (U : X.affineOpens)
    (h : ∀ I : Ideal Γ(X, U.1), I.IsMaximal →
      let pU := (restrictFunctor U.2.isoSpec.inv).map
        ((restrictFunctor U.1.ι).map p)
      Function.Surjective
        (specSectionsLinearMap ((pullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map pU))) :
    Function.Surjective (finFreeSectionsMap' p U.1) := by
  apply finFreeSectionsMap'_surjective_of_app_surjective p U.1
  exact app_affineOpen_surjective_of_coordinate_residue_pullbacks_of_rank
    p hM U h

/-- A coordinate-free form of
`finFreeSectionsMap'_surjective_of_coordinate_residue_pullbacks_of_rank`.  The residue
fibre is here taken directly along the composite morphism from the residue-field
spectrum to `X`; `affineOpenResiduePullbackIso` supplies the comparison with the
coordinate presentation used by affine Nakayama. -/
theorem finFreeSectionsMap'_surjective_of_geometric_residue_pullbacks_of_rank
    {X : Scheme.{u}} {m q : ℕ} {M : X.Modules} [M.IsQuasicoherent]
    (p : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (hM : IsProjectiveOfRank q M) (U : X.affineOpens)
    (h : ∀ I : Ideal Γ(X, U.1), I.IsMaximal →
      let i := U.1.ι
      let j := U.2.isoSpec.inv
      let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      Function.Surjective
        (Hom.app ((pullback (k ≫ (j ≫ i))).map p) ⊤)) :
    Function.Surjective (finFreeSectionsMap' p U.1) := by
  apply finFreeSectionsMap'_surjective_of_coordinate_residue_pullbacks_of_rank
    p hM U
  intro I hI
  let i := U.1.ι
  let j := U.2.isoSpec.inv
  let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let pU := (restrictFunctor j).map ((restrictFunctor i).map p)
  have hpull : Function.Surjective
      (Hom.app ((pullback (k ≫ (j ≫ i))).map p) ⊤) := h I hI
  have hcoordinate : Function.Surjective
      (Hom.app ((pullback k).map pU) ⊤) :=
    surjective_app_of_arrow_iso
      ((pullback k).map pU) ((pullback (k ≫ (j ≫ i))).map p)
      (affineOpenResiduePullbackIso U I
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))))
      (affineOpenResiduePullbackIso U I M)
      (affineOpenResiduePullbackIso_naturality U I p) ⊤ hpull
  exact hcoordinate

end AlgebraicGeometry.Scheme.Modules

end

end
