module

public import StacksAndModuli.API.ClassifyingPrestackFpqcMorphisms

/-!
# Fpqc gluing of morphisms in action quotients

This file lifts fpqc morphism descent from the classifying prestack of principal
bundles to the prestack of principal bundles equipped with an equivariant map to a
fixed group scheme action. Compatibility with the target map is checked after
pulling the fpqc cover back to the total space of the source bundle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]
variable (U : Over S) [ModObj G U]

namespace ActionQuotientObj

variable {G U}

/-- Pull an action-quotient object back along a morphism to its base. -/
noncomputable def pullback (a : ActionQuotientObj G U) {T : Over S}
    (f : T ⟶ a.carrier.base) : ActionQuotientObj G U := by
  let carrier := a.carrier.pullback f
  letI : IsModHom G (a.carrier.pullbackHom f).total :=
    (a.carrier.pullbackHom f).equivariant
  letI : IsModHom G a.map := a.equivariant
  exact
    { carrier := carrier
      map := (a.carrier.pullbackHom f).total ≫ a.map
      equivariant := inferInstance }

/-- The canonical cartesian quotient morphism from a pulled-back object. -/
noncomputable def pullbackHom (a : ActionQuotientObj G U) {T : Over S}
    (f : T ⟶ a.carrier.base) : pullback a f ⟶ a where
  carrier := a.carrier.pullbackHom f
  map_naturality := rfl

/-- The canonical quotient pullback morphism lies over the base-change map. -/
lemma pullbackHom_isHomLift (a : ActionQuotientObj G U) {T : Over S}
    (f : T ⟶ a.carrier.base) :
    IsHomLift (actionQuotientPrestack G U).p f (pullbackHom a f) := by
  apply IsHomLift.of_fac (actionQuotientPrestack G U).p f (pullbackHom a f)
      rfl rfl
  letI := ClassifyingObj.pullbackHom_isHomLift a.carrier f
  exact IsHomLift.fac (classifyingPrestack G).p f (a.carrier.pullbackHom f)

end ActionQuotientObj

namespace ActionQuotientPrestackMorphisms

variable {G U}

/-- Equip the source of a bundle morphism with the map induced from its target
action-quotient object. -/
noncomputable def sourceOfCarrierHom (a : ActionQuotientObj G U)
    {x : ClassifyingObj G} (xi : x ⟶ a.carrier) : ActionQuotientObj G U := by
  letI : IsModHom G xi.total := xi.equivariant
  letI : IsModHom G a.map := a.equivariant
  exact
    { carrier := x
      map := xi.total ≫ a.map
      equivariant := inferInstance }

/-- Regard a bundle morphism as a quotient morphism from its induced source. -/
noncomputable def homOfCarrierHom (a : ActionQuotientObj G U)
    {x : ClassifyingObj G} (xi : x ⟶ a.carrier) :
    sourceOfCarrierHom a xi ⟶ a where
  carrier := xi
  map_naturality := rfl

/-- A bundle lift induces a quotient lift after equipping its source with the
induced target map. -/
lemma homOfCarrierHom_isHomLift (a : ActionQuotientObj G U)
    {T : Over S} {x : ClassifyingObj G} (g : T ⟶ a.carrier.base)
    (xi : x ⟶ a.carrier) (hxi : IsHomLift (classifyingPrestack G).p g xi) :
    IsHomLift (actionQuotientPrestack G U).p g (homOfCarrierHom a xi) := by
  letI hxiI : IsHomLift (classifyingPrestack G).p g xi := hxi
  have hdom := IsHomLift.domain_eq (classifyingPrestack G).p g xi
  subst T
  have hg : g = xi.base :=
    IsHomLift.eq_of_isHomLift (classifyingPrestack G).p g xi
  subst g
  exact Functor.IsHomLift.map (p := (actionQuotientPrestack G U).p)
    (homOfCarrierHom a xi)

/-- Precomposition of bundle morphisms induces a morphism between their induced
action-quotient sources. -/
noncomputable def precompOfCarrierHom (a : ActionQuotientObj G U)
    {x' x : ClassifyingObj G} (chi : x' ⟶ x) (xi : x ⟶ a.carrier) :
    sourceOfCarrierHom a (chi ≫ xi) ⟶ sourceOfCarrierHom a xi where
  carrier := chi
  map_naturality := by
    change chi.total ≫ (xi.total ≫ a.map) =
      (chi.total ≫ xi.total) ≫ a.map
    exact (Category.assoc _ _ _).symm

/-- The induced precomposition morphism lies over the same base morphism as its
bundle carrier. -/
lemma precompOfCarrierHom_isHomLift (a : ActionQuotientObj G U)
    {T' T : Over S} {x' x : ClassifyingObj G} (h : T' ⟶ T)
    (chi : x' ⟶ x) (xi : x ⟶ a.carrier)
    (hchi : IsHomLift (classifyingPrestack G).p h chi) :
    IsHomLift (actionQuotientPrestack G U).p h
      (precompOfCarrierHom a chi xi) := by
  letI hchiI : IsHomLift (classifyingPrestack G).p h chi := hchi
  have hdom := IsHomLift.domain_eq (classifyingPrestack G).p h chi
  have hcod := IsHomLift.codomain_eq (classifyingPrestack G).p h chi
  subst T'
  subst T
  have hh : h = chi.base :=
    IsHomLift.eq_of_isHomLift (classifyingPrestack G).p h chi
  subst h
  exact Functor.IsHomLift.map (p := (actionQuotientPrestack G U).p)
    (precompOfCarrierHom a chi xi)

/-- Compare the actual source of a quotient morphism with the source reconstructed
from its underlying bundle morphism. -/
noncomputable def toSourceOfCarrierHom (a : ActionQuotientObj G U)
    {x : ActionQuotientObj G U} (xi : x ⟶ a) :
    x ⟶ sourceOfCarrierHom a xi.carrier where
  carrier := ClassifyingHom.id x.carrier
  map_naturality := by
    change 𝟙 x.carrier.bundle.P ≫ (xi.carrier.total ≫ a.map) = x.map
    rw [Category.id_comp, xi.map_naturality]

/-- The comparison with the reconstructed source is vertical over the identity. -/
lemma toSourceOfCarrierHom_isHomLift (a : ActionQuotientObj G U)
    {x : ActionQuotientObj G U} (xi : x ⟶ a) :
    IsHomLift (actionQuotientPrestack G U).p (𝟙 x.carrier.base)
      (toSourceOfCarrierHom a xi) := by
  exact Functor.IsHomLift.map (p := (actionQuotientPrestack G U).p)
    (toSourceOfCarrierHom a xi)

/-- Reconstructing the source of a quotient morphism and comparing back recovers
the original morphism. -/
@[simp]
lemma toSourceOfCarrierHom_comp (a : ActionQuotientObj G U)
    {x : ActionQuotientObj G U} (xi : x ⟶ a) :
    toSourceOfCarrierHom a xi ≫ homOfCarrierHom a xi.carrier = xi := by
  apply ActionQuotientHom.ext
  change ClassifyingHom.comp (ClassifyingHom.id x.carrier) xi.carrier =
    xi.carrier
  apply ClassifyingHom.ext <;>
    simp [ClassifyingHom.id, ClassifyingHom.comp]

/-- Morphisms in the action-quotient prestack glue uniquely for the fpqc topology. -/
theorem morphismsGlue_fpqc :
    (actionQuotientPrestack G U).p.MorphismsGlue
      (Scheme.fpqcTopology.over S) := by
  intro T R hR a b ha hb phi hphi hcompat
  change ActionQuotientObj G U at a b
  subst T
  let phiCarrier : ∀ {T : Over S} {g : T ⟶ a.carrier.base}, R g →
      ∀ {x : ClassifyingObj G} (xi : x ⟶ a.carrier),
        IsHomLift (classifyingPrestack G).p g xi → (x ⟶ b.carrier) :=
    fun {_} {g} hg {_} xi hxi ↦
      (phi hg (homOfCarrierHom a xi)
        (homOfCarrierHom_isHomLift a g xi hxi)).carrier
  have phiCarrierLift : ∀ {T : Over S} {g : T ⟶ a.carrier.base}
      (hg : R g) {x : ClassifyingObj G} (xi : x ⟶ a.carrier)
      (hxi : IsHomLift (classifyingPrestack G).p g xi),
      IsHomLift (classifyingPrestack G).p g (phiCarrier hg xi hxi) := by
    intro T g hg x xi hxi
    let xiQ := homOfCarrierHom a xi
    have hxiQ := homOfCarrierHom_isHomLift a g xi hxi
    let q := phi hg xiQ hxiQ
    have hq := hphi hg xiQ hxiQ
    apply IsHomLift.of_fac (classifyingPrestack G).p g q.carrier
      (IsHomLift.domain_eq (actionQuotientPrestack G U).p g q)
      (IsHomLift.codomain_eq (actionQuotientPrestack G U).p g q)
    exact IsHomLift.fac (actionQuotientPrestack G U).p g q
  have phiCarrierCompat : ∀ {T' T : Over S} {g : T ⟶ a.carrier.base}
      (hg : R g) {h : T' ⟶ T} {x' x : ClassifyingObj G}
      (chi : x' ⟶ x) (xi : x ⟶ a.carrier)
      (hxi : IsHomLift (classifyingPrestack G).p g xi)
      (hchi : IsHomLift (classifyingPrestack G).p h chi),
      phiCarrier (R.downward_closed hg h) (chi ≫ xi) inferInstance =
        chi ≫ phiCarrier hg xi hxi := by
    intro T' T g hg h x' x chi xi hxi hchi
    let chiQ := precompOfCarrierHom a chi xi
    have hchiQ := precompOfCarrierHom_isHomLift a h chi xi hchi
    have hcomp : chiQ ≫ homOfCarrierHom a xi =
        homOfCarrierHom a (chi ≫ xi) := by
      apply ActionQuotientHom.ext
      rfl
    have H := hcompat hg chiQ (homOfCarrierHom a xi)
      (homOfCarrierHom_isHomLift a g xi hxi) hchiQ
    cases hcomp
    exact congrArg ActionQuotientHom.carrier H
  obtain ⟨PhiCarrier, hPhiCarrier, huniqCarrier⟩ :=
    ClassifyingPrestackMorphisms.morphismsGlue_fpqc (G := G)
      hR rfl hb phiCarrier phiCarrierLift phiCarrierCompat
  let J := Scheme.fpqcTopology.over S
  let R' : Sieve a.carrier.bundle.P := R.pullback a.carrier.bundle.p
  have hR' : R' ∈ J a.carrier.bundle.P := J.pullback_stable _ hR
  have hU : Presieve.IsSheaf J (yoneda.obj U) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have PhiCarrier_map : PhiCarrier.total ≫ b.map = a.map := by
    apply ((hU R' hR').isSeparatedFor).ext
    intro Z k hk
    let g : Z ⟶ a.carrier.base := k ≫ a.carrier.bundle.p
    have hkg : R g := hk
    let xiCarrier : ClassifyingPrestackMorphisms.pullObj a.carrier g ⟶
        a.carrier := ClassifyingPrestackMorphisms.pullTo a.carrier g
    have hxiCarrier : IsHomLift (classifyingPrestack G).p g xiCarrier :=
      ClassifyingPrestackMorphisms.pullTo_isHomLift a.carrier g
    let x : ActionQuotientObj G U := sourceOfCarrierHom a xiCarrier
    let xi : x ⟶ a := homOfCarrierHom a xiCarrier
    have hxi : IsHomLift (actionQuotientPrestack G U).p g xi :=
      homOfCarrierHom_isHomLift a g xiCarrier hxiCarrier
    have hlocal := hPhiCarrier.2 hkg xiCarrier hxiCarrier
    have hlocalTotal := congrArg ClassifyingHom.total hlocal
    dsimp [x, sourceOfCarrierHom] at hlocalTotal
    change (phi hkg xi hxi).carrier.total =
      xiCarrier.total ≫ PhiCarrier.total at hlocalTotal
    have hmapLocal : (phi hkg xi hxi).carrier.total ≫ b.map =
        xiCarrier.total ≫ a.map := by
      have H := (phi hkg xi hxi).map_naturality
      dsimp [x, sourceOfCarrierHom] at H
      exact H
    change k ≫ (PhiCarrier.total ≫ b.map) = k ≫ a.map
    calc
      k ≫ (PhiCarrier.total ≫ b.map) =
          (ClassifyingPrestackMorphisms.pointSection a.carrier k ≫
            xiCarrier.total) ≫
              (PhiCarrier.total ≫ b.map) := by
              change k ≫ (PhiCarrier.total ≫ b.map) =
                (ClassifyingPrestackMorphisms.pointSection a.carrier k ≫
                  Limits.pullback.fst a.carrier.bundle.p g) ≫
                    (PhiCarrier.total ≫ b.map)
              rw [ClassifyingPrestackMorphisms.pointSection_fst]
      _ = ClassifyingPrestackMorphisms.pointSection a.carrier k ≫
          ((xiCarrier.total ≫ PhiCarrier.total) ≫
            b.map) := by
              simp only [Category.assoc]
      _ = ClassifyingPrestackMorphisms.pointSection a.carrier k ≫
          ((phi hkg xi hxi).carrier.total ≫ b.map) := by rw [hlocalTotal]
      _ = ClassifyingPrestackMorphisms.pointSection a.carrier k ≫
          (xiCarrier.total ≫ a.map) := by rw [hmapLocal]
      _ = (ClassifyingPrestackMorphisms.pointSection a.carrier k ≫
          xiCarrier.total) ≫ a.map :=
            (Category.assoc _ _ _).symm
      _ = k ≫ a.map := by
        change (ClassifyingPrestackMorphisms.pointSection a.carrier k ≫
          Limits.pullback.fst a.carrier.bundle.p g) ≫ a.map = k ≫ a.map
        rw [ClassifyingPrestackMorphisms.pointSection_fst]
  let Phi : a ⟶ b :=
    { carrier := PhiCarrier
      map_naturality := PhiCarrier_map }
  have hPhi : IsHomLift (actionQuotientPrestack G U).p (𝟙 a.carrier.base) Phi := by
    letI hPhiCarrierI : IsHomLift (classifyingPrestack G).p
        (𝟙 a.carrier.base) PhiCarrier := hPhiCarrier.1
    apply IsHomLift.of_fac' (actionQuotientPrestack G U).p
      (𝟙 a.carrier.base) Phi rfl hb
    simpa [Phi] using IsHomLift.fac' (classifyingPrestack G).p
      (𝟙 a.carrier.base) PhiCarrier
  have hfactor : ∀ {T : Over S} {g : T ⟶ a.carrier.base} (hg : R g)
      {x : ActionQuotientObj G U} (xi : x ⟶ a)
      (hxi : IsHomLift (actionQuotientPrestack G U).p g xi),
      phi hg xi hxi = xi ≫ Phi := by
    intro T g hg x xi hxi
    letI hxiI : IsHomLift (actionQuotientPrestack G U).p g xi := hxi
    have hxbase := IsHomLift.domain_eq (actionQuotientPrestack G U).p g xi
    subst T
    apply ActionQuotientHom.ext
    have hxiCarrier : IsHomLift (classifyingPrestack G).p g xi.carrier :=
      BasedFunctor.preserves_isHomLift (actionQuotientPrestack.forget (G := G) (U := U))
        g xi
    let chi := toSourceOfCarrierHom a xi
    have hchi : IsHomLift (actionQuotientPrestack G U).p
        (𝟙 x.carrier.base) chi := toSourceOfCarrierHom_isHomLift a xi
    let xi' := homOfCarrierHom a xi.carrier
    have hxi' : IsHomLift (actionQuotientPrestack G U).p g xi' :=
      homOfCarrierHom_isHomLift a g xi.carrier hxiCarrier
    have H := hcompat (h := 𝟙 x.carrier.base) hg chi xi' hxi' hchi
    have hcomp : chi ≫ xi' = xi := toSourceOfCarrierHom_comp a xi
    have H' : phi hg (chi ≫ xi') inferInstance = chi ≫ phi hg xi' hxi' := by
      simpa only [Category.id_comp] using H
    let Lifted := { q : x ⟶ a //
      IsHomLift (actionQuotientPrestack G U).p g q }
    have hpairs : (⟨chi ≫ xi', inferInstance⟩ : Lifted) = ⟨xi, hxi⟩ := by
      apply Subtype.ext
      exact hcomp
    have hsame := congrArg (fun q : Lifted ↦ phi hg q.1 q.2) hpairs
    have Hactual : phi hg xi hxi = chi ≫ phi hg xi' hxi' :=
      hsame.symm.trans H'
    have Hcarrier := congrArg ActionQuotientHom.carrier Hactual
    have hcarrierComp : (chi ≫ phi hg xi' hxi').carrier =
        (phi hg xi' hxi').carrier := by
      change ClassifyingHom.comp (ClassifyingHom.id x.carrier)
        (phi hg xi' hxi').carrier = (phi hg xi' hxi').carrier
      apply ClassifyingHom.ext <;>
        simp [ClassifyingHom.id, ClassifyingHom.comp]
    rw [hcarrierComp] at Hcarrier
    have hactual : (phi hg xi hxi).carrier =
        phiCarrier hg xi.carrier hxiCarrier := by
      simpa [chi, xi', phiCarrier, toSourceOfCarrierHom,
        ClassifyingHom.id, ClassifyingHom.comp] using Hcarrier
    exact hactual.trans (hPhiCarrier.2 hg xi.carrier hxiCarrier)
  refine ⟨Phi, ⟨hPhi, hfactor⟩, ?_⟩
  intro Psi hPsi
  apply ActionQuotientHom.ext
  apply huniqCarrier Psi.carrier
  constructor
  · letI hPsiI : IsHomLift (actionQuotientPrestack G U).p (𝟙 a.carrier.base) Psi :=
      hPsi.1
    exact BasedFunctor.preserves_isHomLift
      (actionQuotientPrestack.forget (G := G) (U := U))
        (𝟙 a.carrier.base) Psi
  · intro T g hg x xi hxi
    let xi' := homOfCarrierHom a xi
    have hxi' := homOfCarrierHom_isHomLift a g xi hxi
    exact congrArg ActionQuotientHom.carrier (hPsi.2 hg xi' hxi')

end ActionQuotientPrestackMorphisms

end AlgebraicGeometry.Scheme
