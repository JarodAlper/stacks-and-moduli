module

public import StacksAndModuli.«Section4.2-Representability».«part4.2.2-stabilizers»

/-!
# The inertia stack

This module covers the unlabeled definition of the inertia stack,
`eqn:pullback-functor-on-auts` (Equation 4.2.11), `exer:inertia-stack-examples`
(Exercise 4.2.14) and `exer:relative-inertia-properties` (Exercise 4.2.15) of §4.2
(Representability of the diagonal) of *Stacks and Moduli*,
subsection label `sec:stabilizers-and-inertia`
(second half). The inertia definition and `exer:relative-inertia-properties` are
formalized; `eqn:pullback-functor-on-auts` and `exer:inertia-stack-examples` (which
presupposes quotient stacks) are recorded as prose only — see the comments in their
section blocks.

The inertia stack of a prestack `𝒳` is the fiber product `I_𝒳 = 𝒳 ×_{𝒳 × 𝒳} 𝒳` of the
diagonal with itself; the relative inertia of a morphism `F : 𝒳 → 𝒴` is
`I_{𝒳/𝒴} = 𝒳 ×_{𝒳 ×_𝒴 𝒳} 𝒳`, the fiber product of the relative diagonal with itself.

Unlabeled inertia API:
- `CategoryTheory.BasedCategory.inertia` and `CategoryTheory.BasedFunctor.inertia`: the
  inertia stack and the relative inertia stack;
- `CategoryTheory.BasedCategory.inertiaMap`: functoriality `I_𝒳 → I_𝒴`;

Main book results for Exercise 4.2.15:
- `CategoryTheory.BasedFunctor.inertiaUnit`, `inertiaInclusion`,
  `inertiaBaseChangeLift`: the identity section and the two morphisms in part (b);
- `CategoryTheory.BasedFunctor.exists_equivalence_inertiaPairs_inertia`: the explicit
  pair model of relative inertia from part (a);
- `CategoryTheory.BasedFunctor.exists_equivalence_inertia_fiberProduct_inertiaConj`: the
  cartesian description in part (c).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section SecStabilizersAndInertia

open CategoryTheory Functor Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

variable (𝒳 : BasedCategory.{v₂, u₂} 𝒮) in
/-- Background definition for Section 4.2.2 (the unlabeled definition "Inertia
stack"): the inertia stack of a prestack `𝒳` over `𝒮` — the fiber product
`I_𝒳 = 𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` of the diagonal with itself. Its objects over `S` are pairs
of objects `x₁, x₂` of `𝒳` over `S` with an isomorphism `(x₁, x₁) ≅ (x₂, x₂)` over the
identity; over each object it encodes the automorphisms of objects of `𝒳`. -/
abbrev inertia : BasedCategory 𝒮 :=
  fiberProduct (diag 𝒳) (diag 𝒳)

/-- The morphism of inertia stacks induced by a morphism of prestacks `F : 𝒳 → 𝒴`:
`I_𝒳 → I_𝒴`, sending an automorphism `α` of `x` to `F(α)`. -/
abbrev inertiaMap {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) : inertia 𝒳 ⥤ᵇ inertia 𝒴 :=
  fiberProductMap F (prodMap F F) F (eqToIso (diag_comp_prodMap F).symm)
    (eqToIso (diag_comp_prodMap F).symm)

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳) in
/-- Background definition for Definition 4.2.5 (the comparison functor): the fiber of the
inertia stack `I_𝒳 = 𝒳 ×_{𝒳 × 𝒳} 𝒳` over a point `x : Sch/S → 𝒳` maps to the stabilizer
`G_x`, sending `(o, t, γ)` to the pair carrying the automorphism `inAut o` of `o.fst`
transported along `γ`. -/
def inertiaFiberToStabilizer :
    fiberProduct (fiberProductFst (diag 𝒳) (diag 𝒳)) x ⥤ᵇ stabilizer x where
  obj a :=
    { fst := a.fst.fst
      snd := a.snd
      over_eq := a.over_eq
      iso := FiberProductObj.isoMk a.iso (inAut a.fst ≪≫ a.iso)
        (by
          haveI h₁ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj a.fst.fst)) a.iso.hom := a.isHomLift
          haveI h₂ := inAut_isHomLift a.fst
          exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj a.fst.fst)) a.iso.hom _
            h₁ (isHomLift_id_comp 𝒳.p _ _ h₂ h₁))
        (by
          haveI h₁ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj a.fst.fst)) a.iso.hom := a.isHomLift
          haveI h₂ := inAut_isHomLift a.fst
          haveI hc : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj a.fst.fst))
              (inAut a.fst ≪≫ a.iso).hom :=
            isHomLift_id_comp 𝒳.p _ _ h₂ h₁
          haveI i₁ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj a.fst.fst))
              (𝒳.toBase.map a.iso.hom) :=
            BasedFunctor.preserves_isHomLift 𝒳.toBase (𝟙 (𝒳.p.obj a.fst.fst)) a.iso.hom
          haveI i₂ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj a.fst.fst))
              (𝒳.toBase.map (inAut a.fst ≪≫ a.iso).hom) :=
            BasedFunctor.preserves_isHomLift 𝒳.toBase (𝟙 (𝒳.p.obj a.fst.fst)) _
          haveI k₁ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj (x.obj a.snd)))
              (((prodLift x x).obj a.snd).iso.hom) :=
            ((prodLift x x).obj a.snd).isHomLift
          haveI k₂ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj a.fst.fst))
              (((diag 𝒳).obj a.fst.fst).iso.hom) :=
            ((diag 𝒳).obj a.fst.fst).isHomLift
          haveI j₁ := base_isHomLift_comp (S := 𝒳.p.obj a.fst.fst)
            (T := 𝒳.p.obj (x.obj a.snd)) (𝒳.toBase.map a.iso.hom)
            (((prodLift x x).obj a.snd).iso.hom)
          haveI j₂ := base_isHomLift_comp (S := 𝒳.p.obj a.fst.fst)
            (T := 𝒳.p.obj a.fst.fst) (((diag 𝒳).obj a.fst.fst).iso.hom)
            (𝒳.toBase.map (inAut a.fst ≪≫ a.iso).hom)
          exact base_hom_ext (S := 𝒳.p.obj a.fst.fst) (T := 𝒳.p.obj a.fst.fst) _ _)
      isHomLift := FiberProductHom.isHomLift_of_fst _ (𝟙 (𝒳.p.obj a.fst.fst)) a.isHomLift }
  map {a b} ψ :=
    { fst := ψ.fst.fst
      snd := ψ.snd
      isHomLift := ψ.isHomLift
      w := by
        have hf : ψ.fst.fst ≫ b.fst.iso.hom.fst = a.fst.iso.hom.fst ≫ ψ.fst.snd :=
          congrArg FiberProductHom.fst ψ.fst.w
        have hs : ψ.fst.fst ≫ b.fst.iso.hom.snd = a.fst.iso.hom.snd ≫ ψ.fst.snd :=
          congrArg FiberProductHom.snd ψ.fst.w
        have hw : ψ.fst.fst ≫ b.iso.hom = a.iso.hom ≫ x.map ψ.snd := ψ.w
        have hof : a.fst.iso.inv.fst ≫ a.fst.iso.hom.fst = 𝟙 a.fst.snd :=
          congrArg FiberProductHom.fst a.fst.iso.inv_hom_id
        have hof' : b.fst.iso.inv.fst ≫ b.fst.iso.hom.fst = 𝟙 b.fst.snd :=
          congrArg FiberProductHom.fst b.fst.iso.inv_hom_id
        have hoh' : b.fst.iso.hom.fst ≫ b.fst.iso.inv.fst = 𝟙 b.fst.fst :=
          congrArg FiberProductHom.fst b.fst.iso.hom_inv_id
        haveI : IsIso b.fst.iso.hom.fst := ⟨b.fst.iso.inv.fst, hoh', hof'⟩
        have hif : ψ.fst.snd ≫ b.fst.iso.inv.fst =
            a.fst.iso.inv.fst ≫ ψ.fst.fst := by
          rw [← cancel_mono b.fst.iso.hom.fst]
          simp only [Category.assoc, hf, hof', Category.comp_id, reassoc_of% hof]
          exact (Category.id_comp _).symm
        refine FiberProductHom.ext ?_ ?_
        · exact hw
        · change ψ.fst.fst ≫ (b.fst.iso.hom.snd ≫ b.fst.iso.inv.fst) ≫ b.iso.hom =
            ((a.fst.iso.hom.snd ≫ a.fst.iso.inv.fst) ≫ a.iso.hom) ≫ x.map ψ.snd
          rw [Category.assoc, Category.assoc, ← Category.assoc ψ.fst.fst, hs,
            Category.assoc, Category.assoc, reassoc_of% hif, hw] }
  map_id a := by refine FiberProductHom.ext ?_ ?_ <;> rfl
  map_comp f g := by refine FiberProductHom.ext ?_ ?_ <;> rfl
  w := rfl

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳) in
/-- The comparison functor is faithful: a morphism of the inertia fiber is determined by
its second component and the first component of its first. -/
lemma inertiaFiberToStabilizer_faithful : (inertiaFiberToStabilizer x).toFunctor.Faithful := by
  constructor
  intro a b ψ χ h
  have h1' : ((inertiaFiberToStabilizer x).map ψ).fst
      = ((inertiaFiberToStabilizer x).map χ).fst := congrArg _ h
  have h2' : ((inertiaFiberToStabilizer x).map ψ).snd
      = ((inertiaFiberToStabilizer x).map χ).snd := congrArg _ h
  have h1 : ψ.fst.fst = χ.fst.fst := h1'
  have h2 : ψ.snd = χ.snd := h2'
  have hfψ : ψ.fst.fst ≫ b.fst.iso.hom.fst = a.fst.iso.hom.fst ≫ ψ.fst.snd :=
    congrArg FiberProductHom.fst ψ.fst.w
  have hfχ : χ.fst.fst ≫ b.fst.iso.hom.fst = a.fst.iso.hom.fst ≫ χ.fst.snd :=
    congrArg FiberProductHom.fst χ.fst.w
  have hah : a.fst.iso.hom.fst ≫ a.fst.iso.inv.fst = 𝟙 a.fst.fst :=
    congrArg FiberProductHom.fst a.fst.iso.hom_inv_id
  have hai : a.fst.iso.inv.fst ≫ a.fst.iso.hom.fst = 𝟙 a.fst.snd :=
    congrArg FiberProductHom.fst a.fst.iso.inv_hom_id
  haveI : IsIso a.fst.iso.hom.fst := ⟨a.fst.iso.inv.fst, hah, hai⟩
  have h3 : ψ.fst.snd = χ.fst.snd := by
    rw [← cancel_epi a.fst.iso.hom.fst, ← hfψ, ← hfχ, h1]
  exact FiberProductHom.ext (FiberProductHom.ext h1 h3) h2

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳) in
/-- The comparison functor is full. -/
lemma inertiaFiberToStabilizer_full : (inertiaFiberToStabilizer x).toFunctor.Full := by
  constructor
  intro a b q
  have qf : q.fst ≫ b.iso.hom = a.iso.hom ≫ x.map q.snd :=
    congrArg FiberProductHom.fst q.w
  have qs : q.fst ≫ ((inAut b.fst).hom ≫ b.iso.hom) =
      ((inAut a.fst).hom ≫ a.iso.hom) ≫ x.map q.snd :=
    congrArg FiberProductHom.snd q.w
  have hah : a.fst.iso.hom.fst ≫ a.fst.iso.inv.fst = 𝟙 a.fst.fst :=
    congrArg FiberProductHom.fst a.fst.iso.hom_inv_id
  have hbi : b.fst.iso.inv.fst ≫ b.fst.iso.hom.fst = 𝟙 b.fst.snd :=
    congrArg FiberProductHom.fst b.fst.iso.inv_hom_id
  haveI : IsIso b.iso.hom := ⟨b.iso.inv, b.iso.hom_inv_id, b.iso.inv_hom_id⟩
  have key : q.fst ≫ (inAut b.fst).hom = (inAut a.fst).hom ≫ q.fst := by
    rw [← cancel_mono b.iso.hom, Category.assoc, qs, Category.assoc, ← qf,
      Category.assoc]
  -- the lifted morphism
  haveI hinva : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj a.fst.fst)) a.fst.iso.inv.fst := by
    haveI h₀ : IsHomLift (prod 𝒳 𝒳).p (𝟙 (𝒳.p.obj a.fst.fst)) a.fst.iso.hom :=
      a.fst.isHomLift
    haveI h₄ : IsHomLift (prod 𝒳 𝒳).p (𝟙 (𝒳.p.obj a.fst.fst)) a.fst.iso.inv :=
      IsHomLift.lift_id_inv (prod 𝒳 𝒳).p (𝒳.p.obj a.fst.fst) a.fst.iso
    exact FiberProductHom.isHomLift_fst a.fst.iso.inv (𝟙 (𝒳.p.obj a.fst.fst)) h₄
  haveI hbhom : IsHomLift (prod 𝒳 𝒳).p (𝟙 (𝒳.p.obj b.fst.fst)) b.fst.iso.hom :=
    b.fst.isHomLift
  haveI hhomb : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj b.fst.fst)) b.fst.iso.hom.fst :=
    FiberProductHom.isHomLift_fst b.fst.iso.hom (𝟙 (𝒳.p.obj b.fst.fst)) hbhom
  haveI hq : IsHomLift 𝒳.p (𝒳.p.map q.fst) q.fst := inferInstance
  refine ⟨{ fst := { fst := q.fst
                     snd := a.fst.iso.inv.fst ≫ q.fst ≫ b.fst.iso.hom.fst
                     isHomLift := ?_
                     w := ?_ }
            snd := q.snd
            isHomLift := q.isHomLift
            w := qf }, ?_⟩
  · haveI h1 : IsHomLift 𝒳.p (𝒳.p.map q.fst) (q.fst ≫ b.fst.iso.hom.fst) :=
      IsHomLift.comp_lift_id_right' 𝒳.p (𝒳.p.map q.fst) q.fst (𝒳.p.obj b.fst.fst)
        b.fst.iso.hom.fst
    exact IsHomLift.comp_lift_id_left' 𝒳.p (𝒳.p.obj a.fst.fst) a.fst.iso.inv.fst
      (𝒳.p.map q.fst) (q.fst ≫ b.fst.iso.hom.fst)
  · refine FiberProductHom.ext ?_ ?_
    · change q.fst ≫ b.fst.iso.hom.fst =
        a.fst.iso.hom.fst ≫ a.fst.iso.inv.fst ≫ q.fst ≫ b.fst.iso.hom.fst
      rw [← Category.assoc, hah]
      exact (Category.id_comp _).symm
    · change q.fst ≫ b.fst.iso.hom.snd =
        a.fst.iso.hom.snd ≫ a.fst.iso.inv.fst ≫ q.fst ≫ b.fst.iso.hom.fst
      have key' : q.fst ≫ b.fst.iso.hom.snd ≫ b.fst.iso.inv.fst =
          (a.fst.iso.hom.snd ≫ a.fst.iso.inv.fst) ≫ q.fst := key
      calc q.fst ≫ b.fst.iso.hom.snd
          = q.fst ≫ b.fst.iso.hom.snd ≫ b.fst.iso.inv.fst ≫ b.fst.iso.hom.fst := by
            rw [hbi]
            exact congrArg (fun t ↦ q.fst ≫ t) (Category.comp_id _).symm
        _ = (q.fst ≫ b.fst.iso.hom.snd ≫ b.fst.iso.inv.fst) ≫ b.fst.iso.hom.fst := by
            rw [Category.assoc, Category.assoc]
        _ = ((a.fst.iso.hom.snd ≫ a.fst.iso.inv.fst) ≫ q.fst) ≫ b.fst.iso.hom.fst := by
            rw [key']
        _ = a.fst.iso.hom.snd ≫ a.fst.iso.inv.fst ≫ q.fst ≫ b.fst.iso.hom.fst := by
            rw [Category.assoc, Category.assoc]
  · refine FiberProductHom.ext ?_ ?_ <;> rfl

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳) in
/-- The comparison functor is essentially surjective. -/
lemma inertiaFiberToStabilizer_essSurj : (inertiaFiberToStabilizer x).toFunctor.EssSurj := by
  constructor
  intro b
  haveI hb : IsHomLift (prod 𝒳 𝒳).p (𝟙 (𝒳.p.obj b.fst)) b.iso.hom := b.isHomLift
  haveI hbf : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj b.fst)) b.iso.hom.fst :=
    FiberProductHom.isHomLift_fst b.iso.hom (𝟙 (𝒳.p.obj b.fst)) hb
  haveI hbs : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj b.fst)) b.iso.hom.snd :=
    FiberProductHom.isHomLift_snd b.iso.hom (𝟙 (𝒳.p.obj b.fst)) hb
  have hover : 𝒳.p.obj (x.obj b.snd) = 𝒳.p.obj b.fst :=
    (Functor.congr_obj x.w b.snd).trans b.over_eq
  refine ⟨{ fst := { fst := b.fst
                     snd := x.obj b.snd
                     over_eq := hover
                     iso := FiberProductObj.isoMk (FiberProductObj.isoFst b.iso)
                       (FiberProductObj.isoSnd b.iso)
                       (isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj b.fst))
                         b.iso.hom.fst b.iso.hom.snd hbf hbs)
                       ?_
                     isHomLift := ?_ }
            snd := b.snd
            over_eq := b.over_eq
            iso := FiberProductObj.isoFst b.iso
            isHomLift := hbf }, ⟨?_⟩⟩
  · -- base compatibility of the two component isomorphisms
    haveI i₁ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj b.fst))
        (𝒳.toBase.map (FiberProductObj.isoFst b.iso).hom) :=
      BasedFunctor.preserves_isHomLift 𝒳.toBase (𝟙 (𝒳.p.obj b.fst)) b.iso.hom.fst
    haveI i₂ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj b.fst))
        (𝒳.toBase.map (FiberProductObj.isoSnd b.iso).hom) :=
      BasedFunctor.preserves_isHomLift 𝒳.toBase (𝟙 (𝒳.p.obj b.fst)) b.iso.hom.snd
    haveI k₁ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj (x.obj b.snd)))
        (((diag 𝒳).obj (x.obj b.snd)).iso.hom) :=
      ((diag 𝒳).obj (x.obj b.snd)).isHomLift
    haveI k₂ : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj b.fst))
        (((diag 𝒳).obj b.fst).iso.hom) :=
      ((diag 𝒳).obj b.fst).isHomLift
    haveI j₁ := base_isHomLift_comp (S := 𝒳.p.obj b.fst)
      (T := 𝒳.p.obj (x.obj b.snd)) (𝒳.toBase.map (FiberProductObj.isoFst b.iso).hom)
      (((diag 𝒳).obj (x.obj b.snd)).iso.hom)
    haveI j₂ := base_isHomLift_comp (S := 𝒳.p.obj b.fst)
      (T := 𝒳.p.obj b.fst) (((diag 𝒳).obj b.fst).iso.hom)
      (𝒳.toBase.map (FiberProductObj.isoSnd b.iso).hom)
    exact base_hom_ext (S := 𝒳.p.obj b.fst) (T := 𝒳.p.obj b.fst) _ _
  · exact FiberProductHom.isHomLift_of_fst _ (𝟙 (𝒳.p.obj b.fst)) hbf
  · refine FiberProductObj.isoMk (Iso.refl b.fst) (Iso.refl b.snd)
      (isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj b.fst)) (𝟙 b.fst) (𝟙 b.snd)
        (IsHomLift.id rfl) (IsHomLift.id b.over_eq)) ?_
    have hinvhom : b.iso.inv.fst ≫ b.iso.hom.fst = 𝟙 (x.obj b.snd) :=
      congrArg FiberProductHom.fst b.iso.inv_hom_id
    refine FiberProductHom.ext ?_ ?_
    · change 𝟙 b.fst ≫ b.iso.hom.fst = b.iso.hom.fst ≫ x.map (𝟙 b.snd)
      rw [x.toFunctor.map_id]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    · change 𝟙 b.fst ≫ b.iso.hom.snd =
        ((b.iso.hom.snd ≫ b.iso.inv.fst) ≫ b.iso.hom.fst) ≫ x.map (𝟙 b.snd)
      rw [x.toFunctor.map_id]
      have e1 : (b.iso.hom.snd ≫ b.iso.inv.fst) ≫ b.iso.hom.fst = b.iso.hom.snd := by
        rw [Category.assoc, hinvhom]
        exact Category.comp_id _
      exact (Category.id_comp _).trans (e1.symm.trans (Category.comp_id _).symm)

/-- API lemma for Section 4.2.2 (discussion following the unlabeled
definition of the inertia stack): the fiber of the inertia stack over a point — for a
point `x : S → 𝒳` of a prestack, the fiber product of `I_𝒳 → 𝒳` (first projection) and
`x` is equivalent to the stabilizer `G_x`. -/
theorem exists_equivalence_inertia_fiber_stabilizer {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {S : 𝒮} (x : overBased S ⥤ᵇ 𝒳) :
    ∃ E : fiberProduct (fiberProductFst (diag 𝒳) (diag 𝒳)) x ⥤ᵇ stabilizer x,
      E.toFunctor.IsEquivalence := by
  refine ⟨inertiaFiberToStabilizer x, ?_⟩
  let _ := inertiaFiberToStabilizer_faithful x
  let _ := inertiaFiberToStabilizer_full x
  let _ := inertiaFiberToStabilizer_essSurj x
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/- **Section 4.2.2** (`sec:stabilizers-and-inertia`) (deferred part of the discussion
following the definition of the inertia stack): the description of `I_𝒳` as a sheaf of
groups on the big étale site `(Sch/𝒳)_ét`, with `I_𝒳(a) = Aut_S(a)` for `a ∈ 𝒳(S)` — a
"group algebraic space over `𝒳`" incorporating all stabilizers — requires the
`Isom`/`Aut` presheaf of `exer:isom-presheaf` (not started per
`StacksAndModuli/Section3.4-Prestacks/STATUS.md`) and the group-object language
(`CategoryTheory.GrpObj`), and is not formalized here. -/

end CategoryTheory.BasedCategory

end SecStabilizersAndInertia

section EqnPullbackFunctorOnAuts

/- **Equation 4.2.11** (`eqn:pullback-functor-on-auts`): for a morphism `α : a' → a` of a
prestack lying over `S' → S`, there is a pullback map `α* : Aut_S(a) → Aut_{S'}(a')`
sending `β` to the unique dotted arrow `α*(β) : a' → a'` provided by Axiom (2) of a
prestack (`def:prestack`) making `a' --α*(β)--> a' --α--> a` commute with `β ∘ α`, that
is, `α*(β) ≫ α = α ≫ β` in composition order. If `α` is an isomorphism then
`α*(β) = α⁻¹ ∘ β ∘ α` is conjugation by `α`. This equation is proof-internal to the
discussion of the inertia stack; its API belongs to the `Isom`/`Aut` presheaf
(`exer:isom-presheaf`, not started per `StacksAndModuli/Section3.4-Prestacks/STATUS.md`) and no
separate declaration is made here. -/

end EqnPullbackFunctorOnAuts

section ExerInertiaStackExamples

/- Deferred quotient-stack material from Exercise 4.2.14 and the two preceding
unlabeled items:

- Unlabeled exercise (stabilizer group scheme of a quotient stack): for a group scheme
  `G → S` acting on `U → S` with quotient stack `𝒳 = [U/G]`, the square

    `S_U → U`, `I_𝒳 → 𝒳`

  is cartesian, where `S_U → U` is the stabilizer group scheme (the fiber product of the
  action map `(σ, p₂) : G × U → U × U` and the diagonal `U → U × U`).

- Unlabeled example: `I_{B𝔾ₘ} ≅ 𝔾ₘ × B𝔾ₘ`, and for the scaling-times-trivial action of
  `𝔾ₘ` on `𝔾ₘ × 𝔸¹` the inertia of `[𝔸¹/𝔾ₘ]` is `[V(x(t-1))/𝔾ₘ]`.

- `exer:inertia-stack-examples`: (a) `I_{BG} ≅ [G/G]` for conjugation, and
  `I_{BG} ≅ G × BG` for abelian `G`; (b) `I_{[U/G]} ≅ [(G × U)/G]` with
  `g ⋅ (h, u) = (ghg⁻¹, gu)`; (c) for finite constant `G`,
  `I_{[U/G]} = ∐_{g ∈ Conj(G)} [U^g / C_g]`; (d) the explicit computation for
  `[𝔸³/S₃]`.

All of these presuppose quotient stacks `[U/G]` and classifying stacks `BG` (Stacks
Project 04UV, 06FI), which have not been formalized (tracked in the STATUS.md files of
§3.4/§3.5); these items are therefore deferred with them. -/

end ExerInertiaStackExamples

section ExerRelativeInertiaProperties

open CategoryTheory Functor Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

variable (F : 𝒳 ⥤ᵇ 𝒴) in
/-- Background definition for Section 4.2.2 (the unlabeled definition "Inertia
stack", relative case): the relative inertia stack of a morphism of prestacks
`F : 𝒳 → 𝒴` — the fiber product `I_{𝒳/𝒴} = 𝒳 ×_{𝒳 ×_𝒴 𝒳} 𝒳` of the relative diagonal
`Δ_F : 𝒳 → 𝒳 ×_𝒴 𝒳` with itself. -/
abbrev inertia : BasedCategory 𝒮 :=
  fiberProduct F.diag F.diag

variable (F : 𝒳 ⥤ᵇ 𝒴) in
/-- **Exercise 4.2.15** (`exer:relative-inertia-properties`) (part (a), identity
section): the identity section `𝒳 → I_{𝒳/𝒴}` of the relative inertia stack of
`F : 𝒳 → 𝒴`, sending an object `x` to `(x, id_x)`. -/
abbrev inertiaUnit : 𝒳 ⥤ᵇ F.inertia :=
  fiberProductLift (BasedFunctor.id 𝒳) (BasedFunctor.id 𝒳)
    (Iso.refl ((BasedFunctor.id 𝒳).comp F.diag))

variable (F : 𝒳 ⥤ᵇ 𝒴) in
/-- **Exercise 4.2.15** (`exer:relative-inertia-properties`) (part (b), first morphism):
the canonical morphism `I_{𝒳/𝒴} → I_𝒳` from the relative inertia stack of `F : 𝒳 → 𝒴` to
the (absolute) inertia stack of `𝒳`, regarding an automorphism `α` of `x` with
`F(α) = id` as an automorphism of `x`. -/
abbrev inertiaInclusion : F.inertia ⥤ᵇ BasedCategory.inertia 𝒳 :=
  fiberProductMap (BasedFunctor.id 𝒳)
    (prodLift (fiberProductFst F F) (fiberProductSnd F F)) (BasedFunctor.id 𝒳)
    (eqToIso (by
      rw [BasedFunctor.id_comp, comp_prodLift, fiberProductLift_comp_fst,
        fiberProductLift_comp_snd]))
    (eqToIso (by
      rw [BasedFunctor.id_comp, comp_prodLift, fiberProductLift_comp_fst,
        fiberProductLift_comp_snd]))

/-- API lemma for Exercise 4.2.15 (part (b), over `𝒳`): the
morphism `I_{𝒳/𝒴} → I_𝒳` commutes with the projections to `𝒳` — it is a morphism over
`𝒳`. -/
@[simp]
lemma inertiaInclusion_comp_fiberProductFst (F : 𝒳 ⥤ᵇ 𝒴) :
    F.inertiaInclusion.comp (fiberProductFst (BasedCategory.diag 𝒳) (BasedCategory.diag 𝒳)) =
      fiberProductFst F.diag F.diag := by
  rw [inertiaInclusion, fiberProductMap_comp_fst, BasedFunctor.comp_id]

variable (F : 𝒳 ⥤ᵇ 𝒴) in
/-- **Exercise 4.2.15** (`exer:relative-inertia-properties`) (part (b), second morphism):
the canonical morphism `I_𝒳 → I_𝒴 ×_𝒴 𝒳` from the inertia stack of `𝒳` to the base
change to `𝒳` of the inertia stack of `𝒴` along `F : 𝒳 → 𝒴` — the pair of the induced
morphism `I_𝒳 → I_𝒴` and the projection `I_𝒳 → 𝒳`. -/
abbrev inertiaBaseChangeLift :
    BasedCategory.inertia 𝒳 ⥤ᵇ
      fiberProduct (fiberProductFst (BasedCategory.diag 𝒴) (BasedCategory.diag 𝒴)) F :=
  fiberProductLift (inertiaMap F) (fiberProductFst (BasedCategory.diag 𝒳) (BasedCategory.diag 𝒳))
    (eqToIso (fiberProductMap_comp_fst _ _ _ _ _))

/-- API lemma for Exercise 4.2.15 (part (b), over `𝒳`): the
morphism `I_𝒳 → I_𝒴 ×_𝒴 𝒳` commutes with the projections to `𝒳` — it is a morphism over
`𝒳`. -/
@[simp]
lemma inertiaBaseChangeLift_comp_fiberProductSnd (F : 𝒳 ⥤ᵇ 𝒴) :
    F.inertiaBaseChangeLift.comp
        (fiberProductSnd (fiberProductFst (BasedCategory.diag 𝒴) (BasedCategory.diag 𝒴)) F) =
      fiberProductFst (BasedCategory.diag 𝒳) (BasedCategory.diag 𝒳) :=
  fiberProductLift_comp_snd _ _ _

/- Deferred group-theoretic part of Exercise 4.2.15(b): over a field-valued point
`x ∈ 𝒳(K)` the morphisms
`I_{𝒳/𝒴} → I_𝒳 → I_𝒴 ×_𝒴 𝒳` restrict on fibers to a left exact sequence
`1 → K_x → G_x → G_{F(x)}` of group algebraic spaces.
The exactness statement requires the group structure on stabilizers (the `Isom` presheaf
of `exer:isom-presheaf`, not started per `StacksAndModuli/Section3.4-Prestacks/STATUS.md`, and
group objects in étale sheaves) and is not formalized; the fibers themselves are
identified in
`CategoryTheory.BasedCategory.exists_equivalence_inertia_fiber_stabilizer` and
`CategoryTheory.BasedCategory.exists_equivalence_fiberProduct_diag_stabilizerUnit`. -/

end CategoryTheory.BasedFunctor

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- Background definition for Exercise 4.2.15 (part (a), objects of the
explicit model): an object of the explicit model of the relative inertia stack of a
morphism of prestacks `F : 𝒳 → 𝒴` — a pair `(x, α)` of an object `x` of `𝒳` and an
automorphism `α : x ≅ x` lying over the identity with `F(α) = id`. -/
structure InertiaPairObj (F : 𝒳 ⥤ᵇ 𝒴) where
  /-- The underlying object of `𝒳`. -/
  obj : 𝒳.obj
  /-- The automorphism. -/
  aut : obj ≅ obj
  /-- The automorphism lies over the identity. -/
  isHomLift : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj obj)) aut.hom
  /-- The automorphism is killed by `F`. -/
  map_aut_hom : F.map aut.hom = 𝟙 (F.obj obj)

attribute [instance] InertiaPairObj.isHomLift

variable {F : 𝒳 ⥤ᵇ 𝒴}

/-- Background definition for Exercise 4.2.15 (part (a), morphisms of the
explicit model): a morphism `(x, α) → (y, β)` of pairs in the explicit model of the
relative inertia — a morphism `x → y` of `𝒳` commuting with the automorphisms. -/
@[ext]
structure InertiaPairHom (a b : InertiaPairObj F) where
  /-- The underlying morphism of `𝒳`. -/
  hom : a.obj ⟶ b.obj
  /-- Compatibility with the automorphisms. -/
  w : hom ≫ b.aut.hom = a.aut.hom ≫ hom := by cat_disch

/-- The identity morphism of a pair. -/
@[simps]
def InertiaPairHom.id (a : InertiaPairObj F) : InertiaPairHom a a where
  hom := 𝟙 a.obj
  w := by simp

/-- Composition of morphisms of pairs. -/
@[simps]
def InertiaPairHom.comp {a b c : InertiaPairObj F} (f : InertiaPairHom a b)
    (g : InertiaPairHom b c) : InertiaPairHom a c where
  hom := f.hom ≫ g.hom
  w := by rw [Category.assoc, g.w, ← Category.assoc, f.w, Category.assoc]

/-- The category of pairs `(x, α)` with `α` an automorphism of `x` killed by `F`. -/
instance InertiaPairObj.instCategory : Category (InertiaPairObj F) where
  Hom a b := InertiaPairHom a b
  id a := InertiaPairHom.id a
  comp f g := f.comp g
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

@[simp]
lemma InertiaPairObj.id_hom (a : InertiaPairObj F) :
    InertiaPairHom.hom (𝟙 a) = 𝟙 a.obj :=
  rfl

@[simp]
lemma InertiaPairObj.comp_hom {a b c : InertiaPairObj F} (f : a ⟶ b) (g : b ⟶ c) :
    InertiaPairHom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

variable (F) in
/-- Background definition for Exercise 4.2.15 (part (a), the explicit
model): the explicit model of the relative inertia stack of a morphism of prestacks
`F : 𝒳 → 𝒴` — the category of pairs `(x, α)` with `α` an automorphism of `x` over the
identity killed by `F`, as a based category over `𝒮`. -/
def inertiaPairs : BasedCategory 𝒮 where
  obj := InertiaPairObj F
  p :=
    { obj := fun a ↦ 𝒳.p.obj a.obj
      map := fun f ↦ 𝒳.p.map (InertiaPairHom.hom f)
      map_id := fun a ↦ 𝒳.p.map_id a.obj
      map_comp := fun f g ↦ 𝒳.p.map_comp (InertiaPairHom.hom f) (InertiaPairHom.hom g) }

variable (F) in
/-- Background definition for Exercise 4.2.15 (part (a), identity section
of the explicit model): the identity section of the explicit model of the relative
inertia — the morphism `𝒳 → I_{𝒳/𝒴}` sending an object `x` to the pair `(x, id_x)`. -/
def inertiaPairsUnit : 𝒳 ⥤ᵇ inertiaPairs F where
  obj x :=
    { obj := x
      aut := Iso.refl x
      isHomLift := IsHomLift.id rfl
      map_aut_hom := by simp }
  map φ := { hom := φ, w := by simp }
  map_id x := InertiaPairHom.ext rfl
  map_comp φ ψ := InertiaPairHom.ext rfl
  w := rfl

variable (F) in
/-- Candidate comparison functor: pairs model → relative inertia. -/
def inertiaPairsToInertia : inertiaPairs F ⥤ᵇ F.inertia where
  obj a :=
    { fst := a.obj
      snd := a.obj
      over_eq := rfl
      iso := FiberProductObj.isoMk a.aut (Iso.refl a.obj)
        (isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj a.obj)) a.aut.hom (𝟙 a.obj)
          a.isHomLift (IsHomLift.id rfl))
        (by
          rw [a.map_aut_hom]
          exact (Category.id_comp _).trans (((Category.comp_id _).symm).trans
            (congrArg (fun t ↦ (F.diag.obj a.obj).iso.hom ≫ t)
              (F.toFunctor.map_id a.obj).symm)))
      isHomLift := by
        apply FiberProductHom.isHomLift_of_fst _ (𝟙 (𝒳.p.obj a.obj))
        exact a.isHomLift }
  map {a b} h :=
    { fst := h.hom
      snd := h.hom
      isHomLift := inferInstance
      w := by
        refine FiberProductHom.ext h.w ?_
        change h.hom ≫ 𝟙 b.obj = 𝟙 a.obj ≫ h.hom
        simp }
  map_id a := by refine FiberProductHom.ext ?_ ?_ <;> rfl
  map_comp f g := by refine FiberProductHom.ext ?_ ?_ <;> rfl
  w := rfl

lemma inertiaPairsToInertia_faithful (F : 𝒳 ⥤ᵇ 𝒴) :
    (inertiaPairsToInertia F).toFunctor.Faithful := by
  constructor
  intro a b f g h
  exact InertiaPairHom.ext (congrArg FiberProductHom.fst h)

lemma inertiaPairsToInertia_full (F : 𝒳 ⥤ᵇ 𝒴) :
    (inertiaPairsToInertia F).toFunctor.Full := by
  constructor
  intro a b q
  have hsnd : q.fst ≫ 𝟙 b.obj = 𝟙 a.obj ≫ q.snd := congrArg FiberProductHom.snd q.w
  have hfst : q.fst ≫ b.aut.hom = a.aut.hom ≫ q.snd := congrArg FiberProductHom.fst q.w
  have hq : q.fst = q.snd :=
    (Category.comp_id q.fst).symm.trans (hsnd.trans (Category.id_comp q.snd))
  refine ⟨{ hom := q.fst, w := ?_ }, ?_⟩
  · rw [hfst, hq]
  · refine FiberProductHom.ext rfl ?_
    exact hq

lemma inertiaPairsToInertia_essSurj (F : 𝒳 ⥤ᵇ 𝒴) :
    (inertiaPairsToInertia F).toFunctor.EssSurj := by
  constructor
  intro o
  -- the two component isomorphisms of `o.iso`
  have hhomfst : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj o.fst)) o.iso.hom.fst :=
    FiberProductHom.isHomLift_fst o.iso.hom (𝟙 (𝒳.p.obj o.fst)) o.isHomLift
  have hiso : IsHomLift (fiberProduct F F).p (𝟙 (𝒳.p.obj o.fst)) o.iso.hom := o.isHomLift
  have hinv : IsHomLift (fiberProduct F F).p (𝟙 (𝒳.p.obj o.fst)) o.iso.inv := by
    have := hiso
    exact IsHomLift.lift_id_inv (fiberProduct F F).p (𝒳.p.obj o.fst) o.iso
  have hinvsnd : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj o.fst)) o.iso.inv.snd :=
    FiberProductHom.isHomLift_snd o.iso.inv (𝟙 (𝒳.p.obj o.fst)) hinv
  have hhomsnd : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj o.fst)) o.iso.hom.snd :=
    FiberProductHom.isHomLift_snd o.iso.hom (𝟙 (𝒳.p.obj o.fst)) o.isHomLift
  -- components of hom_inv_id / inv_hom_id
  have hhi : o.iso.hom.snd ≫ o.iso.inv.snd = 𝟙 o.fst :=
    congrArg FiberProductHom.snd o.iso.hom_inv_id
  have hih : o.iso.inv.snd ≫ o.iso.hom.snd = 𝟙 o.snd :=
    congrArg FiberProductHom.snd o.iso.inv_hom_id
  -- `F` identifies the two components
  have hw : F.map o.iso.hom.fst ≫ (F.diag.obj o.snd).iso.hom =
      (F.diag.obj o.fst).iso.hom ≫ F.map o.iso.hom.snd := o.iso.hom.w
  have hFeq : F.map o.iso.hom.fst = F.map o.iso.hom.snd :=
    ((Category.comp_id (F.map o.iso.hom.fst)).symm.trans hw).trans
      (Category.id_comp (F.map o.iso.hom.snd))
  refine ⟨{ obj := o.fst
            aut := (FiberProductObj.isoFst (F := F) (G := F) o.iso) ≪≫
              (FiberProductObj.isoSnd (F := F) (G := F) o.iso).symm
            isHomLift := isHomLift_id_comp 𝒳.p _ _ hhomfst hinvsnd
            map_aut_hom := ?_ }, ⟨?_⟩⟩
  · change F.map (o.iso.hom.fst ≫ o.iso.inv.snd) = 𝟙 (F.obj o.fst)
    rw [F.toFunctor.map_comp, hFeq, ← F.toFunctor.map_comp, hhi]
    exact F.toFunctor.map_id o.fst
  · refine FiberProductObj.isoMk (Iso.refl o.fst)
        (FiberProductObj.isoSnd (F := F) (G := F) o.iso) ?_ ?_
    · exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj o.fst)) (𝟙 o.fst) o.iso.hom.snd
        (IsHomLift.id rfl) hhomsnd
    · refine FiberProductHom.ext ?_ ?_
      · change 𝟙 o.fst ≫ o.iso.hom.fst =
          (o.iso.hom.fst ≫ o.iso.inv.snd) ≫ o.iso.hom.snd
        rw [Category.assoc, hih]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      · change 𝟙 o.fst ≫ o.iso.hom.snd = 𝟙 o.fst ≫ o.iso.hom.snd
        rfl

/-- **Exercise 4.2.15** (`exer:relative-inertia-properties`) (part (a)): the relative
inertia stack is the stack of pairs `(x, α)` with `F(α) = id` — for a morphism of
prestacks `F : 𝒳 → 𝒴`, the explicit category of pairs is equivalent to the relative
inertia `I_{𝒳/𝒴} = 𝒳 ×_{𝒳 ×_𝒴 𝒳} 𝒳`, compatibly with the identity sections. -/
theorem exists_equivalence_inertiaPairs_inertia (F : 𝒳 ⥤ᵇ 𝒴) :
    ∃ E : inertiaPairs F ⥤ᵇ F.inertia, E.toFunctor.IsEquivalence ∧
      Nonempty ((inertiaPairsUnit F).comp E ≅ F.inertiaUnit) := by
  refine ⟨inertiaPairsToInertia F, ?_, ?_⟩
  · let _ := inertiaPairsToInertia_faithful F
    let _ := inertiaPairsToInertia_full F
    let _ := inertiaPairsToInertia_essSurj F
    exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  · exact ⟨Iso.refl _⟩

end CategoryTheory.BasedFunctor

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- The underlying automorphism of the first component of an object of the inertia stack:
an object of `I_𝒴` is a pair `(y₁, y₂)` with an isomorphism `(y₁, y₁) ≅ (y₂, y₂)` in
`𝒴 × 𝒴`, and comparing the two component isomorphisms `y₁ ≅ y₂` yields an automorphism
of `y₁`. -/
def inertiaObjAut
    (o : FiberProductObj (BasedCategory.diag 𝒴) (BasedCategory.diag 𝒴)) :
    o.fst ≅ o.fst :=
  FiberProductObj.isoSnd o.iso ≪≫ (FiberProductObj.isoFst o.iso).symm

variable (F : 𝒳 ⥤ᵇ 𝒴) in
/-- Background definition for Exercise 4.2.15 (part (c), the conjugation
morphism of the hint): the conjugation morphism `I_𝒴 ×_𝒴 𝒳 → 𝒳 ×_𝒴 𝒳` — it sends a
quadruple `(y, α, x, β)`, an automorphism `α` of `y ∈ 𝒴` together with `x ∈ 𝒳` and an
isomorphism `β : y ≅ F(x)`, to the triple `(x, x, β ∘ α ∘ β⁻¹)`. -/
def inertiaConj :
    fiberProduct (fiberProductFst (BasedCategory.diag 𝒴) (BasedCategory.diag 𝒴)) F ⥤ᵇ
      fiberProduct F F :=
  fiberProductLift
    (fiberProductSnd (fiberProductFst (BasedCategory.diag 𝒴) (BasedCategory.diag 𝒴)) F)
    (fiberProductSnd (fiberProductFst (BasedCategory.diag 𝒴) (BasedCategory.diag 𝒴)) F)
    (BasedNatIso.mkNatIso
      (NatIso.ofComponents
        (fun o ↦ o.iso.symm ≪≫ inertiaObjAut o.fst ≪≫ o.iso)
        (fun {o o'} ψ ↦ by
          change F.map ψ.snd ≫ o'.iso.inv ≫
              (o'.fst.iso.hom.snd ≫ o'.fst.iso.inv.fst) ≫ o'.iso.hom =
            (o.iso.inv ≫ (o.fst.iso.hom.snd ≫ o.fst.iso.inv.fst) ≫ o.iso.hom) ≫
              F.map ψ.snd
          have hw : ψ.fst.fst ≫ o'.iso.hom = o.iso.hom ≫ F.map ψ.snd := ψ.w
          have hs : ψ.fst.fst ≫ o'.fst.iso.hom.snd =
              o.fst.iso.hom.snd ≫ ψ.fst.snd :=
            congrArg FiberProductHom.snd ψ.fst.w
          have hf : ψ.fst.fst ≫ o'.fst.iso.hom.fst =
              o.fst.iso.hom.fst ≫ ψ.fst.snd :=
            congrArg FiberProductHom.fst ψ.fst.w
          have hof : o.fst.iso.inv.fst ≫ o.fst.iso.hom.fst = 𝟙 o.fst.snd :=
            congrArg FiberProductHom.fst o.fst.iso.inv_hom_id
          have hof' : o'.fst.iso.inv.fst ≫ o'.fst.iso.hom.fst = 𝟙 o'.fst.snd :=
            congrArg FiberProductHom.fst o'.fst.iso.inv_hom_id
          have hoh' : o'.fst.iso.hom.fst ≫ o'.fst.iso.inv.fst = 𝟙 o'.fst.fst :=
            congrArg FiberProductHom.fst o'.fst.iso.hom_inv_id
          haveI : IsIso o'.fst.iso.hom.fst := ⟨o'.fst.iso.inv.fst, hoh', hof'⟩
          have hif : o.fst.iso.inv.fst ≫ ψ.fst.fst =
              ψ.fst.snd ≫ o'.fst.iso.inv.fst := by
            rw [← cancel_mono o'.fst.iso.hom.fst]
            simp only [Category.assoc, hf, hof', Category.comp_id, reassoc_of% hof]
            exact Category.id_comp _
          have hw' : F.map ψ.snd = o.iso.inv ≫ ψ.fst.fst ≫ o'.iso.hom := by
            rw [hw, Iso.inv_hom_id_assoc]
          rw [hw']
          simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hs]
          rw [← reassoc_of% hif]))
      (fun o ↦ by
        haveI h₁ : IsHomLift 𝒴.p (𝟙 (𝒴.p.obj o.fst.fst)) o.iso.hom := o.isHomLift
        haveI h₂ : IsHomLift 𝒴.p (𝟙 (𝒴.p.obj o.fst.fst)) o.iso.inv :=
          IsHomLift.lift_id_inv 𝒴.p (𝒴.p.obj o.fst.fst) o.iso
        haveI h₃ : IsHomLift (BasedCategory.prod 𝒴 𝒴).p (𝟙 (𝒴.p.obj o.fst.fst))
            o.fst.iso.hom :=
          o.fst.isHomLift
        haveI h₄ : IsHomLift (BasedCategory.prod 𝒴 𝒴).p (𝟙 (𝒴.p.obj o.fst.fst))
            o.fst.iso.inv :=
          IsHomLift.lift_id_inv (BasedCategory.prod 𝒴 𝒴).p (𝒴.p.obj o.fst.fst) o.fst.iso
        haveI h₅ : IsHomLift 𝒴.p (𝟙 (𝒴.p.obj o.fst.fst)) o.fst.iso.hom.snd :=
          FiberProductHom.isHomLift_snd o.fst.iso.hom (𝟙 (𝒴.p.obj o.fst.fst)) h₃
        haveI h₆ : IsHomLift 𝒴.p (𝟙 (𝒴.p.obj o.fst.fst)) o.fst.iso.inv.fst :=
          FiberProductHom.isHomLift_fst o.fst.iso.inv (𝟙 (𝒴.p.obj o.fst.fst)) h₄
        have h₇ := isHomLift_id_comp 𝒴.p o.fst.iso.hom.snd o.fst.iso.inv.fst h₅ h₆
        have h₈ := isHomLift_id_comp 𝒴.p
          (o.fst.iso.hom.snd ≫ o.fst.iso.inv.fst) o.iso.hom h₇ h₁
        exact isHomLift_id_comp 𝒴.p o.iso.inv
          ((o.fst.iso.hom.snd ≫ o.fst.iso.inv.fst) ≫ o.iso.hom) h₂ h₈))

/-- The objectwise comparison identifying conjugation of the image of an inertia object
with its relative diagonal. Its two components reverse the two components of the inertia
isomorphism. -/
def inertiaCartesianIsoApp (F : 𝒳 ⥤ᵇ 𝒴)
    (q : (BasedCategory.inertia 𝒳).obj) :
    F.inertiaConj.obj (F.inertiaBaseChangeLift.obj q) ≅ F.diag.obj q.snd := by
  let e₁ : q.fst ≅ q.snd := FiberProductObj.isoSnd q.iso
  let e₂ : q.fst ≅ q.snd := FiberProductObj.isoFst q.iso
  apply FiberProductObj.isoMk e₁ e₂
  · have hq : IsHomLift (BasedCategory.prod 𝒳 𝒳).p
        (𝟙 (𝒳.p.obj q.fst)) q.iso.hom := q.isHomLift
    have h₁ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj q.fst)) e₁.hom := by
      exact FiberProductHom.isHomLift_snd q.iso.hom (𝟙 (𝒳.p.obj q.fst)) hq
    have h₂ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj q.fst)) e₂.hom := by
      exact FiberProductHom.isHomLift_fst q.iso.hom (𝟙 (𝒳.p.obj q.fst)) hq
    exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj q.fst)) e₁.hom e₂.hom h₁ h₂
  · dsimp [e₁, e₂]
    let a : q.fst ⟶ q.snd := q.iso.hom.fst
    let b : q.fst ⟶ q.snd := q.iso.hom.snd
    let ai : q.snd ⟶ q.fst := q.iso.inv.fst
    have hdiag : (F.diag.obj q.snd).iso.hom = 𝟙 (F.obj q.snd) := by rfl
    have hd : (F.inertiaBaseChangeLift.obj q).iso.hom = 𝟙 (F.obj q.fst) := by rfl
    let δ : F.obj q.fst ≅ F.obj q.fst := (F.inertiaBaseChangeLift.obj q).iso
    have hδ : δ = Iso.refl _ := by
      apply Iso.ext
      exact hd
    have hconj : (F.inertiaConj.obj (F.inertiaBaseChangeLift.obj q)).iso.hom =
        F.map b ≫ F.map ai := by
      dsimp [BasedFunctor.inertiaConj, BasedFunctor.inertiaObjAut,
        BasedCategory.fiberProductLift, BasedNatIso.mkNatIso,
        NatIso.ofComponents, BasedNatTrans.forgetful, Iso.trans]
      have hsnd : (FiberProductObj.isoSnd ((BasedCategory.inertiaMap F).obj q).iso).hom =
          F.map b := by
        have auxHom {L R : 𝒳 ⥤ᵇ BasedCategory.prod 𝒴 𝒴} (h : L = R) (z : 𝒳.obj) :
            ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
              (eqToIso h)).app z).hom).snd =
                eqToHom (congrArg (fun K ↦ (K.obj z).snd) h) := by
          subst R
          rfl
        have auxInv {L R : 𝒳 ⥤ᵇ BasedCategory.prod 𝒴 𝒴} (h : L = R) (z : 𝒳.obj) :
            ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
              (eqToIso h)).app z).inv).snd =
                eqToHom (congrArg (fun K ↦ (K.obj z).snd) h.symm) := by
          subst R
          rfl
        have hτhom (z : 𝒳.obj) :
            ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
              (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app z).hom).snd =
                𝟙 (F.obj z) := by
          rw [auxHom]
          have hp : congrArg (fun K ↦ (K.obj z).snd)
              (BasedCategory.diag_comp_prodMap F).symm = rfl := Subsingleton.elim _ _
          rw [hp]
          rfl
        have hτinv (z : 𝒳.obj) :
            ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
              (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app z).inv).snd =
                𝟙 (F.obj z) := by
          rw [auxInv]
          have hp : congrArg (fun K ↦ (K.obj z).snd)
              (BasedCategory.diag_comp_prodMap F) = rfl := Subsingleton.elim _ _
          rw [hp]
          rfl
        dsimp [BasedCategory.inertiaMap, BasedCategory.fiberProductMap,
          BasedCategory.fiberProductLift, BasedCategory.whiskerLeftIso,
          BasedCategory.whiskerRightIso, BasedNatIso.mkNatIso,
          BasedNatTrans.forgetful, BasedNatTrans.comp, NatTrans.vcomp,
          NatIso.ofComponents, Iso.trans, FiberProductObj.isoSnd]
        change
          ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
              (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app q.fst).hom).snd ≫
            F.map q.iso.hom.snd ≫
          ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
              (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app q.snd).inv).snd =
            F.map b
        rw [hτhom, hτinv]
        change 𝟙 (F.obj q.fst) ≫ F.map b ≫ 𝟙 (F.obj q.snd) = F.map b
        simp
      have hfst : (FiberProductObj.isoFst ((BasedCategory.inertiaMap F).obj q).iso).inv =
          F.map ai := by
        have auxHom {L R : 𝒳 ⥤ᵇ BasedCategory.prod 𝒴 𝒴} (h : L = R) (z : 𝒳.obj) :
            ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
              (eqToIso h)).app z).hom).fst =
                eqToHom (congrArg (fun K ↦ (K.obj z).fst) h) := by
          subst R
          rfl
        have auxInv {L R : 𝒳 ⥤ᵇ BasedCategory.prod 𝒴 𝒴} (h : L = R) (z : 𝒳.obj) :
            ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
              (eqToIso h)).app z).inv).fst =
                eqToHom (congrArg (fun K ↦ (K.obj z).fst) h.symm) := by
          subst R
          rfl
        have hτhom (z : 𝒳.obj) :
            ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
              (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app z).hom).fst =
                𝟙 (F.obj z) := by
          rw [auxHom]
          have hp : congrArg (fun K ↦ (K.obj z).fst)
              (BasedCategory.diag_comp_prodMap F).symm = rfl := Subsingleton.elim _ _
          rw [hp]
          rfl
        have hτinv (z : 𝒳.obj) :
            ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
              (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app z).inv).fst =
                𝟙 (F.obj z) := by
          rw [auxInv]
          have hp : congrArg (fun K ↦ (K.obj z).fst)
              (BasedCategory.diag_comp_prodMap F) = rfl := Subsingleton.elim _ _
          rw [hp]
          rfl
        have hrawHom (z : 𝒳.obj) :
            ((eqToHom (BasedCategory.diag_comp_prodMap F).symm :
              F.comp (BasedCategory.diag 𝒴) ⟶
                (BasedCategory.diag 𝒳).comp (BasedCategory.prodMap F F)).toNatTrans.app z).fst =
              𝟙 (F.obj z) := by
          exact hτhom z
        have hrawInv (z : 𝒳.obj) :
            ((eqToHom (BasedCategory.diag_comp_prodMap F) :
              (BasedCategory.diag 𝒳).comp (BasedCategory.prodMap F F) ⟶
                F.comp (BasedCategory.diag 𝒴)).toNatTrans.app z).fst =
              𝟙 (F.obj z) := by
          exact hτinv z
        dsimp [BasedCategory.inertiaMap, BasedCategory.fiberProductMap,
          BasedCategory.fiberProductLift, BasedCategory.whiskerLeftIso,
          BasedCategory.whiskerRightIso, BasedNatIso.mkNatIso,
          BasedNatTrans.forgetful, BasedNatTrans.comp, NatTrans.vcomp,
          NatIso.ofComponents, Iso.trans, FiberProductObj.isoFst,
          BasedCategory.fiberProductIsoComm, BasedFunctor.comp,
          BasedCategory.prodMap, BasedCategory.prodLift,
          BasedCategory.fiberProductFst]
        rw [hrawHom, hrawInv]
        have hident : (𝟙 (F.obj q.snd) ≫ F.map ai) ≫ 𝟙 (F.obj q.fst) = F.map ai := by
          simp
        simpa only [ai] using hident
      rw [hsnd, hfst]
      change δ.inv ≫ ((F.map b ≫ F.map ai) ≫ δ.hom) = F.map b ≫ F.map ai
      rw [hδ]
      simp
    have hc : ai ≫ a = 𝟙 q.snd := by
      exact congrArg FiberProductHom.fst q.iso.inv_hom_id
    have halg : F.map b ≫ 𝟙 (F.obj q.snd) =
        (F.map b ≫ F.map ai) ≫ F.map a := by
      rw [Category.comp_id, Category.assoc, ← F.toFunctor.map_comp, hc,
        F.toFunctor.map_id, Category.comp_id]
    simpa only [a, b, ai, FiberProductObj.isoFst, FiberProductObj.isoSnd,
      hdiag, hconj] using halg

/-- The natural isomorphism whose universal fiber-product lift is the cartesian comparison
from `I_𝒳` to the pullback of the conjugation morphism along the relative diagonal. -/
def inertiaCartesianIso (F : 𝒳 ⥤ᵇ 𝒴) :
    F.inertiaBaseChangeLift.comp F.inertiaConj ≅
      (fiberProductSnd (BasedCategory.diag 𝒳) (BasedCategory.diag 𝒳)).comp F.diag :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents (inertiaCartesianIsoApp F) (fun {q r} φ ↦ by
      apply FiberProductHom.ext
      · change φ.fst ≫ r.iso.hom.snd = q.iso.hom.snd ≫ φ.snd
        exact congrArg FiberProductHom.snd φ.w
      · change φ.fst ≫ r.iso.hom.fst = q.iso.hom.fst ≫ φ.snd
        exact congrArg FiberProductHom.fst φ.w))
    (fun q ↦ by
      have hq : IsHomLift (BasedCategory.prod 𝒳 𝒳).p
          (𝟙 (𝒳.p.obj q.fst)) q.iso.hom := q.isHomLift
      have h : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj q.fst)) q.iso.hom.snd :=
        FiberProductHom.isHomLift_snd q.iso.hom (𝟙 (𝒳.p.obj q.fst)) hq
      exact FiberProductHom.isHomLift_of_fst (inertiaCartesianIsoApp F q).hom
        (𝟙 (𝒳.p.obj q.fst)) h)

/-- The first component of the objectwise cartesian comparison is the second component of
the inertia isomorphism. -/
@[simp]
lemma inertiaCartesianIsoApp_hom_fst (F : 𝒳 ⥤ᵇ 𝒴)
    (q : (BasedCategory.inertia 𝒳).obj) :
    (inertiaCartesianIsoApp F q).hom.fst = q.iso.hom.snd := rfl

/-- The second component of the objectwise cartesian comparison is the first component of
the inertia isomorphism. -/
@[simp]
lemma inertiaCartesianIsoApp_hom_snd (F : 𝒳 ⥤ᵇ 𝒴)
    (q : (BasedCategory.inertia 𝒳).obj) :
    (inertiaCartesianIsoApp F q).hom.snd = q.iso.hom.fst := rfl

/-- Background definition for Exercise 4.2.15 (part (c), the comparison
morphism): the canonical morphism from `I_𝒳` to the pullback of the conjugation morphism
`I_𝒴 ×_𝒴 𝒳 → 𝒳 ×_𝒴 𝒳` along the relative diagonal. -/
def inertiaCartesianComparison (F : 𝒳 ⥤ᵇ 𝒴) :
    BasedCategory.inertia 𝒳 ⥤ᵇ fiberProduct F.inertiaConj F.diag :=
  fiberProductLift F.inertiaBaseChangeLift
    (fiberProductSnd (BasedCategory.diag 𝒳) (BasedCategory.diag 𝒳))
    (inertiaCartesianIso F)

/-- The cartesian comparison for inertia is faithful. -/
lemma inertiaCartesianComparison_faithful (F : 𝒳 ⥤ᵇ 𝒴) :
    (inertiaCartesianComparison F).toFunctor.Faithful := by
  constructor
  intro q r φ ψ h
  apply FiberProductHom.ext
  · exact congrArg (fun k ↦ k.fst.snd) h
  · exact congrArg (fun k ↦ k.snd) h

/-- The first component of the comparison isomorphism in the image of an inertia object. -/
lemma inertiaMap_obj_iso_hom_fst (F : 𝒳 ⥤ᵇ 𝒴)
    (q : (BasedCategory.inertia 𝒳).obj) :
    ((BasedCategory.inertiaMap F).obj q).iso.hom.fst = F.map q.iso.hom.fst := by
  have auxHom {L R : 𝒳 ⥤ᵇ BasedCategory.prod 𝒴 𝒴} (h : L = R) (z : 𝒳.obj) :
      ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso h)).app z).hom).fst =
          eqToHom (congrArg (fun K ↦ (K.obj z).fst) h) := by
    subst R
    rfl
  have auxInv {L R : 𝒳 ⥤ᵇ BasedCategory.prod 𝒴 𝒴} (h : L = R) (z : 𝒳.obj) :
      ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso h)).app z).inv).fst =
          eqToHom (congrArg (fun K ↦ (K.obj z).fst) h.symm) := by
    subst R
    rfl
  have hτhom (z : 𝒳.obj) :
      ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app z).hom).fst =
          𝟙 (F.obj z) := by
    rw [auxHom]
    have hp : congrArg (fun K ↦ (K.obj z).fst)
        (BasedCategory.diag_comp_prodMap F).symm = rfl := Subsingleton.elim _ _
    rw [hp]
    rfl
  have hτinv (z : 𝒳.obj) :
      ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app z).inv).fst =
          𝟙 (F.obj z) := by
    rw [auxInv]
    have hp : congrArg (fun K ↦ (K.obj z).fst)
        (BasedCategory.diag_comp_prodMap F) = rfl := Subsingleton.elim _ _
    rw [hp]
    rfl
  dsimp [BasedCategory.inertiaMap, BasedCategory.fiberProductMap,
    BasedCategory.fiberProductLift, BasedCategory.whiskerLeftIso,
    BasedCategory.whiskerRightIso, BasedNatIso.mkNatIso,
    BasedNatTrans.forgetful, BasedNatTrans.comp, NatTrans.vcomp,
    NatIso.ofComponents, Iso.trans, FiberProductObj.isoFst]
  change
    ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app q.fst).hom).fst ≫
      F.map q.iso.hom.fst ≫
    ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app q.snd).inv).fst =
      F.map q.iso.hom.fst
  rw [hτhom, hτinv]
  let a : q.fst ⟶ q.snd := q.iso.hom.fst
  change 𝟙 (F.obj q.fst) ≫ (F.map a ≫ 𝟙 (F.obj q.snd)) = F.map a
  simp

/-- The second component of the comparison isomorphism in the image of an inertia object. -/
lemma inertiaMap_obj_iso_hom_snd (F : 𝒳 ⥤ᵇ 𝒴)
    (q : (BasedCategory.inertia 𝒳).obj) :
    ((BasedCategory.inertiaMap F).obj q).iso.hom.snd = F.map q.iso.hom.snd := by
  have auxHom {L R : 𝒳 ⥤ᵇ BasedCategory.prod 𝒴 𝒴} (h : L = R) (z : 𝒳.obj) :
      ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso h)).app z).hom).snd =
          eqToHom (congrArg (fun K ↦ (K.obj z).snd) h) := by
    subst R
    rfl
  have auxInv {L R : 𝒳 ⥤ᵇ BasedCategory.prod 𝒴 𝒴} (h : L = R) (z : 𝒳.obj) :
      ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso h)).app z).inv).snd =
          eqToHom (congrArg (fun K ↦ (K.obj z).snd) h.symm) := by
    subst R
    rfl
  have hτhom (z : 𝒳.obj) :
      ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app z).hom).snd =
          𝟙 (F.obj z) := by
    rw [auxHom]
    have hp : congrArg (fun K ↦ (K.obj z).snd)
        (BasedCategory.diag_comp_prodMap F).symm = rfl := Subsingleton.elim _ _
    rw [hp]
    rfl
  have hτinv (z : 𝒳.obj) :
      ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app z).inv).snd =
          𝟙 (F.obj z) := by
    rw [auxInv]
    have hp : congrArg (fun K ↦ (K.obj z).snd)
        (BasedCategory.diag_comp_prodMap F) = rfl := Subsingleton.elim _ _
    rw [hp]
    rfl
  dsimp [BasedCategory.inertiaMap, BasedCategory.fiberProductMap,
    BasedCategory.fiberProductLift, BasedCategory.whiskerLeftIso,
    BasedCategory.whiskerRightIso, BasedNatIso.mkNatIso,
    BasedNatTrans.forgetful, BasedNatTrans.comp, NatTrans.vcomp,
    NatIso.ofComponents, Iso.trans, FiberProductObj.isoSnd]
  change
    ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app q.fst).hom).snd ≫
      F.map q.iso.hom.snd ≫
    ((((BasedNatTrans.forgetful 𝒳 (BasedCategory.prod 𝒴 𝒴)).mapIso
        (eqToIso (BasedCategory.diag_comp_prodMap F).symm)).app q.snd).inv).snd =
      F.map q.iso.hom.snd
  rw [hτhom, hτinv]
  let a : q.fst ⟶ q.snd := q.iso.hom.snd
  change 𝟙 (F.obj q.fst) ≫ (F.map a ≫ 𝟙 (F.obj q.snd)) = F.map a
  simp

/-- The cartesian comparison for inertia is full. -/
lemma inertiaCartesianComparison_full (F : 𝒳 ⥤ᵇ 𝒴) :
    (inertiaCartesianComparison F).toFunctor.Full := by
  constructor
  intro q r k
  let φ : q ⟶ r :=
    { fst := k.fst.snd
      snd := k.snd
      isHomLift := by
        exact isHomLift_map_of_common_lift
          ((fiberProduct (fiberProductFst (BasedCategory.diag 𝒴)
            (BasedCategory.diag 𝒴)) F).p.map k.fst)
          k.fst.snd k.snd k.fst.isHomLift k.isHomLift
      w := by
        have hw₁ := congrArg FiberProductHom.fst k.w
        have hw₂ := congrArg FiberProductHom.snd k.w
        change k.fst.snd ≫ r.iso.hom.snd = q.iso.hom.snd ≫ k.snd at hw₁
        change k.fst.snd ≫ r.iso.hom.fst = q.iso.hom.fst ≫ k.snd at hw₂
        exact FiberProductHom.ext hw₂ hw₁ }
  refine ⟨φ, ?_⟩
  apply FiberProductHom.ext
  · apply FiberProductHom.ext
    · apply FiberProductHom.ext
      · have hw := k.fst.w
        let u : F.obj q.fst ⟶ F.obj r.fst := k.fst.fst.fst
        let p : q.fst ⟶ r.fst := k.fst.snd
        let δq : F.obj q.fst ≅ F.obj q.fst := (F.inertiaBaseChangeLift.obj q).iso
        let δr : F.obj r.fst ≅ F.obj r.fst := (F.inertiaBaseChangeLift.obj r).iso
        have hδq : δq = Iso.refl _ := by
          apply Iso.ext
          rfl
        have hδr : δr = Iso.refl _ := by
          apply Iso.ext
          rfl
        change u ≫ δr.hom = δq.hom ≫ F.map p at hw
        rw [hδq, hδr] at hw
        change u ≫ 𝟙 (F.obj r.fst) = 𝟙 (F.obj q.fst) ≫ F.map p at hw
        have hup : F.map p = u := by
          simpa only [Category.comp_id, Category.id_comp] using hw.symm
        change F.map p = u
        exact hup
      · let p : q.fst ⟶ r.fst := k.fst.snd
        let s : q.snd ⟶ r.snd := k.snd
        let u : F.obj q.fst ⟶ F.obj r.fst := k.fst.fst.fst
        let v : F.obj q.snd ⟶ F.obj r.snd := k.fst.fst.snd
        let aq : q.fst ⟶ q.snd := q.iso.hom.fst
        let aqi : q.snd ⟶ q.fst := q.iso.inv.fst
        let ar : r.fst ⟶ r.snd := r.iso.hom.fst
        have hdu := k.fst.w
        let δq : F.obj q.fst ≅ F.obj q.fst := (F.inertiaBaseChangeLift.obj q).iso
        let δr : F.obj r.fst ≅ F.obj r.fst := (F.inertiaBaseChangeLift.obj r).iso
        have hδq : δq = Iso.refl _ := by
          apply Iso.ext
          rfl
        have hδr : δr = Iso.refl _ := by
          apply Iso.ext
          rfl
        change u ≫ δr.hom = δq.hom ≫ F.map p at hdu
        rw [hδq, hδr] at hdu
        change u ≫ 𝟙 (F.obj r.fst) = 𝟙 (F.obj q.fst) ≫ F.map p at hdu
        have hu : u = F.map p := by
          simpa only [Category.comp_id, Category.id_comp] using hdu
        have hiy := congrArg FiberProductHom.fst k.fst.fst.w
        change u ≫ ((BasedCategory.inertiaMap F).obj r).iso.hom.fst =
          ((BasedCategory.inertiaMap F).obj q).iso.hom.fst ≫ v at hiy
        rw [inertiaMap_obj_iso_hom_fst, inertiaMap_obj_iso_hom_fst] at hiy
        change u ≫ F.map ar = F.map aq ≫ v at hiy
        rw [hu] at hiy
        have hx := congrArg FiberProductHom.snd k.w
        change p ≫ ar = aq ≫ s at hx
        have hmap : F.map p ≫ F.map ar = F.map aq ≫ F.map s := by
          rw [← F.toFunctor.map_comp, hx, F.toFunctor.map_comp]
        have hv : F.map aq ≫ v = F.map aq ≫ F.map s := hiy.symm.trans hmap
        have ha : aq ≫ aqi = 𝟙 q.fst :=
          congrArg FiberProductHom.fst q.iso.hom_inv_id
        have hai : aqi ≫ aq = 𝟙 q.snd :=
          congrArg FiberProductHom.fst q.iso.inv_hom_id
        haveI : IsIso aq := ⟨aqi, ha, hai⟩
        haveI : IsIso (F.map aq) := by infer_instance
        have hvs : v = F.map s := by
          rw [← cancel_epi (F.map aq)]
          exact hv
        change F.map s = v
        exact hvs.symm
    · rfl
  · rfl

/-- The cartesian comparison for inertia is essentially surjective. -/
lemma inertiaCartesianComparison_essSurj (F : 𝒳 ⥤ᵇ 𝒴) :
    (inertiaCartesianComparison F).toFunctor.EssSurj := by
  constructor
  intro t
  let e₁ : t.fst.snd ≅ t.snd := FiberProductObj.isoSnd t.iso
  let e₂ : t.fst.snd ≅ t.snd := FiberProductObj.isoFst t.iso
  let e : (BasedCategory.diag 𝒳).obj t.fst.snd ≅
      (BasedCategory.diag 𝒳).obj t.snd := by
    apply FiberProductObj.isoMk e₁ e₂
    · have ht : IsHomLift (fiberProduct F F).p
          (𝟙 (𝒳.p.obj t.fst.snd)) t.iso.hom := by
        have ht' := t.isHomLift
        rw [← t.fst.over_eq] at ht'
        exact ht'
      have h₁ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.snd)) e₁.hom :=
        FiberProductHom.isHomLift_snd t.iso.hom _ ht
      have h₂ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.snd)) e₂.hom :=
        FiberProductHom.isHomLift_fst t.iso.hom _ ht
      exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj t.fst.snd))
        e₁.hom e₂.hom h₁ h₂
    · haveI ht : IsHomLift (fiberProduct F F).p
          (𝟙 (𝒳.p.obj t.fst.snd)) t.iso.hom := by
        have ht' := t.isHomLift
        rw [← t.fst.over_eq] at ht'
        exact ht'
      haveI h₁ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.snd)) e₁.hom :=
        FiberProductHom.isHomLift_snd t.iso.hom _ ht
      haveI h₂ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.snd)) e₂.hom :=
        FiberProductHom.isHomLift_fst t.iso.hom _ ht
      haveI i₁ : IsHomLift (BasedCategory.base 𝒮).p
          (𝟙 (𝒳.p.obj t.fst.snd)) (𝒳.toBase.map e₁.hom) :=
        BasedFunctor.preserves_isHomLift 𝒳.toBase _ _
      haveI i₂ : IsHomLift (BasedCategory.base 𝒮).p
          (𝟙 (𝒳.p.obj t.fst.snd)) (𝒳.toBase.map e₂.hom) :=
        BasedFunctor.preserves_isHomLift 𝒳.toBase _ _
      haveI is : IsHomLift (BasedCategory.base 𝒮).p
          (𝟙 (𝒳.p.obj t.fst.snd))
          ((BasedCategory.diag 𝒳).obj t.fst.snd).iso.hom :=
        ((BasedCategory.diag 𝒳).obj t.fst.snd).isHomLift
      haveI it : IsHomLift (BasedCategory.base 𝒮).p
          (𝟙 (𝒳.p.obj t.fst.snd))
          ((BasedCategory.diag 𝒳).obj t.snd).iso.hom := by
        rw [t.fst.over_eq, ← t.over_eq]
        exact ((BasedCategory.diag 𝒳).obj t.snd).isHomLift
      haveI il := base_isHomLift_comp (S := 𝒳.p.obj t.fst.snd)
        (T := 𝒳.p.obj t.fst.snd) (𝒳.toBase.map e₁.hom)
        ((BasedCategory.diag 𝒳).obj t.snd).iso.hom
      haveI ir := base_isHomLift_comp (S := 𝒳.p.obj t.fst.snd)
        (T := 𝒳.p.obj t.fst.snd)
        ((BasedCategory.diag 𝒳).obj t.fst.snd).iso.hom (𝒳.toBase.map e₂.hom)
      exact base_hom_ext (S := 𝒳.p.obj t.fst.snd)
        (T := 𝒳.p.obj t.fst.snd) _ _
  let q : (BasedCategory.inertia 𝒳).obj :=
    { fst := t.fst.snd
      snd := t.snd
      over_eq := t.over_eq.trans t.fst.over_eq.symm
      iso := e
      isHomLift := by
        have ht : IsHomLift (fiberProduct F F).p
            (𝟙 (𝒳.p.obj t.fst.snd)) t.iso.hom := by
          have ht' := t.isHomLift
          rw [← t.fst.over_eq] at ht'
          exact ht'
        have h₁ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj t.fst.snd)) e₁.hom :=
          FiberProductHom.isHomLift_snd t.iso.hom _ ht
        exact FiberProductHom.isHomLift_of_fst e.hom _ h₁ }
  refine ⟨q, ⟨?_⟩⟩
  let A : t.fst.snd ≅ t.snd := FiberProductObj.isoFst t.iso
  let B : t.fst.snd ≅ t.snd := FiberProductObj.isoSnd t.iso
  let β : t.fst.fst.fst ≅ F.obj t.fst.snd := t.fst.iso
  let C : t.fst.fst.fst ≅ t.fst.fst.snd := FiberProductObj.isoFst t.fst.fst.iso
  let D : t.fst.fst.fst ≅ t.fst.fst.snd := FiberProductObj.isoSnd t.fst.fst.iso
  let FA : F.obj t.fst.snd ≅ F.obj t.snd := F.toFunctor.mapIso A
  let FB : F.obj t.fst.snd ≅ F.obj t.snd := F.toFunctor.mapIso B
  let γ₁ : ((BasedCategory.inertiaMap F).obj q).fst ≅ t.fst.fst.fst := β.symm
  let γ₂ : ((BasedCategory.inertiaMap F).obj q).snd ≅ t.fst.fst.snd :=
    FA.symm ≪≫ β.symm ≪≫ D
  let iyIso : (BasedCategory.inertiaMap F).obj q ≅ t.fst.fst := by
    apply FiberProductObj.isoMk γ₁ γ₂
    · let S : 𝒮 := 𝒴.p.obj t.fst.fst.fst
      have hβ : IsHomLift 𝒴.p (𝟙 S) β.hom := t.fst.isHomLift
      have hγ₁ : IsHomLift 𝒴.p (𝟙 S) γ₁.hom :=
        IsHomLift.lift_id_inv 𝒴.p S β
      have ht : IsHomLift (fiberProduct F F).p (𝟙 S) t.iso.hom := t.isHomLift
      have hA : IsHomLift 𝒳.p (𝟙 S) A.hom :=
        FiberProductHom.isHomLift_fst t.iso.hom _ ht
      have hAi : IsHomLift 𝒳.p (𝟙 S) A.inv :=
        IsHomLift.lift_id_inv 𝒳.p S A
      have hFAi : IsHomLift 𝒴.p (𝟙 S) FA.inv := by
        exact BasedFunctor.preserves_isHomLift F _ _
      have hD : IsHomLift 𝒴.p (𝟙 S) D.hom := by
        exact FiberProductHom.isHomLift_snd t.fst.fst.iso.hom _ t.fst.fst.isHomLift
      have hγ₂ : IsHomLift 𝒴.p (𝟙 S) γ₂.hom := by
        exact isHomLift_id_comp 𝒴.p _ _
          hFAi (isHomLift_id_comp 𝒴.p _ _ hγ₁ hD)
      exact isHomLift_map_of_common_lift (𝟙 S) γ₁.hom γ₂.hom hγ₁ hγ₂
    · let K : F.obj t.fst.snd ≅ F.obj t.fst.snd :=
        β.symm ≪≫ (D ≪≫ C.symm) ≪≫ β
      have hconj : (F.inertiaConj.obj t.fst).iso = K := by
        rfl
      have houter := t.iso.hom.w
      have hdiag : (F.diag.obj t.snd).iso.hom = 𝟙 (F.obj t.snd) := by
        rfl
      change FA.hom ≫ (F.diag.obj t.snd).iso.hom =
        (F.inertiaConj.obj t.fst).iso.hom ≫ FB.hom at houter
      rw [hdiag, hconj] at houter
      have houter' : FA.hom = K.hom ≫ FB.hom := by
        simpa only [Category.comp_id] using houter
      have hiso : FA = K ≪≫ FB := by
        apply Iso.ext
        exact houter'
      apply FiberProductHom.ext
      · change γ₁.hom ≫ C.hom =
          ((BasedCategory.inertiaMap F).obj q).iso.hom.fst ≫ γ₂.hom
        rw [inertiaMap_obj_iso_hom_fst]
        change β.inv ≫ C.hom = FB.hom ≫ FA.inv ≫ β.inv ≫ D.hom
        rw [hiso]
        simp [K]
      · change γ₁.hom ≫ D.hom =
          ((BasedCategory.inertiaMap F).obj q).iso.hom.snd ≫ γ₂.hom
        rw [inertiaMap_obj_iso_hom_snd]
        change β.inv ≫ D.hom = FA.hom ≫ FA.inv ≫ β.inv ≫ D.hom
        simp
  let dIso : F.inertiaBaseChangeLift.obj q ≅ t.fst := by
    apply FiberProductObj.isoMk (a := F.inertiaBaseChangeLift.obj q) (b := t.fst)
      iyIso (Iso.refl t.fst.snd)
    · let S : 𝒮 := 𝒴.p.obj t.fst.fst.fst
      have hβ : IsHomLift 𝒴.p (𝟙 S) β.hom := t.fst.isHomLift
      have hγ₁ : IsHomLift 𝒴.p (𝟙 S) γ₁.hom :=
        IsHomLift.lift_id_inv 𝒴.p S β
      have hiy : IsHomLift (BasedCategory.inertia 𝒴).p (𝟙 S) iyIso.hom :=
        FiberProductHom.isHomLift_of_fst iyIso.hom _ hγ₁
      have hx : IsHomLift 𝒳.p (𝟙 S) (𝟙 t.fst.snd) :=
        IsHomLift.id t.fst.over_eq
      exact isHomLift_map_of_common_lift (𝟙 S) iyIso.hom (𝟙 t.fst.snd) hiy hx
    · let δ : F.obj t.fst.snd ≅ F.obj t.fst.snd :=
        (F.inertiaBaseChangeLift.obj q).iso
      have hδ : δ = Iso.refl _ := by
        apply Iso.ext
        rfl
      change γ₁.hom ≫ β.hom = δ.hom ≫ F.map (𝟙 t.fst.snd)
      rw [hδ, F.toFunctor.map_id]
      simp only [Iso.refl_hom, Category.id_comp]
      change β.inv ≫ β.hom = 𝟙 (F.obj t.fst.snd)
      exact β.inv_hom_id
  apply FiberProductObj.isoMk (a := (inertiaCartesianComparison F).obj q) (b := t)
    dIso (Iso.refl t.snd)
  · let S : 𝒮 := 𝒴.p.obj t.fst.fst.fst
    have hβ : IsHomLift 𝒴.p (𝟙 S) β.hom := t.fst.isHomLift
    have hγ₁ : IsHomLift 𝒴.p (𝟙 S) γ₁.hom :=
      IsHomLift.lift_id_inv 𝒴.p S β
    have hiy : IsHomLift (BasedCategory.inertia 𝒴).p (𝟙 S) iyIso.hom :=
      FiberProductHom.isHomLift_of_fst iyIso.hom _ hγ₁
    have hd : IsHomLift
        (fiberProduct (fiberProductFst (BasedCategory.diag 𝒴)
          (BasedCategory.diag 𝒴)) F).p (𝟙 S) dIso.hom :=
      FiberProductHom.isHomLift_of_fst dIso.hom _ hiy
    have hx : IsHomLift 𝒳.p (𝟙 S) (𝟙 t.snd) :=
      IsHomLift.id t.over_eq
    exact isHomLift_map_of_common_lift (𝟙 S) dIso.hom (𝟙 t.snd) hd hx
  · apply FiberProductHom.ext
    · change (𝟙 t.fst.snd) ≫ A.hom = q.iso.hom.snd ≫ 𝟙 t.snd
      change (𝟙 t.fst.snd) ≫ A.hom = A.hom ≫ 𝟙 t.snd
      simp
    · change (𝟙 t.fst.snd) ≫ B.hom = q.iso.hom.fst ≫ 𝟙 t.snd
      change (𝟙 t.fst.snd) ≫ B.hom = B.hom ≫ 𝟙 t.snd
      simp

/-- **Exercise 4.2.15** (`exer:relative-inertia-properties`) (part (c)): the inertia
stack as a base change — for a morphism of prestacks `F : 𝒳 → 𝒴` there is a cartesian
square identifying `I_𝒳` with the fiber product of the conjugation morphism
`I_𝒴 ×_𝒴 𝒳 → 𝒳 ×_𝒴 𝒳` and the relative diagonal `Δ_F : 𝒳 → 𝒳 ×_𝒴 𝒳`. -/
theorem exists_equivalence_inertia_fiberProduct_inertiaConj (F : 𝒳 ⥤ᵇ 𝒴) :
    ∃ E : BasedCategory.inertia 𝒳 ⥤ᵇ fiberProduct F.inertiaConj F.diag,
      E.toFunctor.IsEquivalence := by
  refine ⟨inertiaCartesianComparison F, ?_⟩
  let _ := inertiaCartesianComparison_faithful F
  let _ := inertiaCartesianComparison_full F
  let _ := inertiaCartesianComparison_essSurj F
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end CategoryTheory.BasedFunctor

end ExerRelativeInertiaProperties
