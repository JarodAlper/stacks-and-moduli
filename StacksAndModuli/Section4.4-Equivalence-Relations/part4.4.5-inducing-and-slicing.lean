module

public import StacksAndModuli.API.OpenSubstackEquivalence
public import StacksAndModuli.API.RelativelyRepresentableMonomorphism
public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.4-algebraicity»

/-!
# Inducing and slicing presentations

This module formalizes the subsection "Inducing and slicing presentations" of §4.4
(Equivalence relations and groupoids) of *Stacks and Moduli*,
section label
`subsec:equivalence-relations`: the restriction of a groupoid along a morphism `U' → U`
and the slicing exercise, **Exercise 4.4.20** (`exer:slicing-groupoid`). The Borel
construction with **Exercise 4.4.19** (`exer:changing-quotient-stack-presentation`), and
**Exercise 4.4.21** (`exer:stack-of-elliptic-curves-is-finite-quotient`), are not
formalized; their section blocks hold comments recording what is deferred and why
(completeness state: see this folder's STATUS.md).

Main results:
- statements (proofs deferred) of **Exercise 4.4.20** (`exer:slicing-groupoid`): the
  fiber-product description of `R|_{U'}`, the transfer of étaleness/smoothness, the
  open-immersion property of `[U'/R|_{U'}] → [U/R]`, and the isomorphism criterion via
  orbits.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExerChangingQuotientStackPresentation

/- Unformalized Exercise 4.4.19, together with the unlabelled Borel-construction prose
preceding it: for a subgroup `H ⊆ G` of a
smooth affine algebraic group acting on a scheme `X`, the Borel construction
`G ×^H X := (G × X)/H` (a quotient by a free action, hence an algebraic space) carries a
`G`-action with `[X/H] ≅ [(G ×^H X)/G]` (the *induced presentation*). This requires the
quotient-stack machinery `[X/G]` (deferred in §3.4/§4.1, pending the principal-bundle
theory of Appendix B), quotients by free actions (Corollary 4.6.8,
`cor:quotient-stacks-are-dm`, §4.6), and the comparison of the two presentations.
Cf. Stacks Project 04WX. -/

end ExerChangingQuotientStackPresentation

section ExerSlicingGroupoid

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.PresheafGroupoid

variable (𝒢 : PresheafGroupoid.{u}) {U' : Scheme.{u}ᵒᵖ ⥤ Type u} (g : U' ⟶ 𝒢.U)

/-- Background definition used by Exercise 4.4.20: the *restriction* `R|_{U'} ⇉ U'` of
a groupoid of presheaves `s, t : R ⇉ U` along a morphism `g : U' → U`: the relations over
`T` are the triples `(a, b, r)` of two points `a, b ∈ U'(T)` and a relation `r ∈ R(T)`
with `s(r) = g(a)` and `t(r) = g(b)` — the fiber product of `(s, t) : R → U × U` with
`g × g : U' × U' → U × U`. -/
def restrict : PresheafGroupoid.{u} where
  U := U'
  R :=
    { obj := fun T ↦ {p : (U'.obj T × U'.obj T) × 𝒢.R.obj T //
        𝒢.s.app T p.2 = g.app T p.1.1 ∧ 𝒢.t.app T p.2 = g.app T p.1.2}
      map := fun {T T'} f ↦ ↾fun p ↦ ⟨⟨⟨U'.map f p.1.1.1, U'.map f p.1.1.2⟩, 𝒢.R.map f p.1.2⟩,
        by rw [PresheafGroupoid.s_app_map, p.2.1, NatTrans.naturality_apply],
        by rw [PresheafGroupoid.t_app_map, p.2.2, NatTrans.naturality_apply]⟩
      map_id := fun T ↦ by
        ext p
        · simp
        · simp
        · simp
      map_comp := fun {T T' T''} f f' ↦ by
        ext p
        · simp
        · simp
        · simp }
  s := { app := fun T ↦ ↾fun p ↦ p.1.1.1 }
  t := { app := fun T ↦ ↾fun p ↦ p.1.1.2 }
  comp {T} x y h :=
    ⟨⟨⟨y.1.1.1, x.1.1.2⟩, 𝒢.comp x.1.2 y.1.2 (by
      rw [x.2.1, y.2.2]
      exact congrArg (g.app T) h)⟩, by
        rw [PresheafGroupoid.s_comp, y.2.1], by
        rw [PresheafGroupoid.t_comp, x.2.2]⟩
  s_comp {T} x y h := rfl
  t_comp {T} x y h := rfl
  comp_naturality {T T'} f x y h h' := by
    refine Subtype.ext (Prod.ext rfl ?_)
    exact 𝒢.comp_naturality f x.1.2 y.1.2 _ _
  comp_assoc {T} x y z hxy hyz h₁ h₂ := by
    refine Subtype.ext (Prod.ext (Prod.ext rfl rfl) ?_)
    exact 𝒢.comp_assoc x.1.2 y.1.2 z.1.2 _ _ _ _
  e :=
    { app := fun T ↦ ↾fun a ↦ ⟨⟨⟨a, a⟩, 𝒢.e.app T (g.app T a)⟩, by simp, by simp⟩
      naturality := fun {T T'} f ↦ by
        ext a
        · rfl
        · rfl
        · change 𝒢.e.app T' (g.app T' (U'.map f a)) = 𝒢.R.map f (𝒢.e.app T (g.app T a))
          rw [PresheafGroupoid.map_e_app, NatTrans.naturality_apply] }
  e_s := by
    ext T a
    rfl
  e_t := by
    ext T a
    rfl
  comp_e {T} x h := by
    refine Subtype.ext (Prod.ext rfl ?_)
    exact 𝒢.comp_e_app _ _ _
  e_comp {T} x h := by
    refine Subtype.ext (Prod.ext rfl ?_)
    exact 𝒢.e_app_comp _ _ _
  inv :=
    { app := fun T ↦ ↾fun p ↦ ⟨⟨⟨p.1.1.2, p.1.1.1⟩, 𝒢.inv.app T p.1.2⟩,
        by rw [PresheafGroupoid.s_app_inv_app, p.2.2],
        by rw [PresheafGroupoid.t_app_inv_app, p.2.1]⟩
      naturality := fun {T T'} f ↦ by
        ext p
        · rfl
        · rfl
        · exact (𝒢.map_inv_app f p.1.2).symm }
  inv_s := by
    ext T p
    rfl
  inv_t := by
    ext T p
    rfl
  inv_comp {T} x h := by
    refine Subtype.ext (Prod.ext (Prod.ext rfl rfl) ?_)
    change 𝒢.comp (𝒢.inv.app T x.1.2) x.1.2 _ = 𝒢.e.app T (g.app T x.1.1.1)
    simp only [𝒢.inv_comp]
    rw [x.2.1]
  comp_inv {T} x h := by
    refine Subtype.ext (Prod.ext (Prod.ext rfl rfl) ?_)
    change 𝒢.comp x.1.2 (𝒢.inv.app T x.1.2) _ = 𝒢.e.app T (g.app T x.1.1.2)
    simp only [𝒢.comp_inv]
    rw [x.2.2]

/-- Background construction used in part (3) of Exercise 4.4.20: the morphism of quotient
prestacks
`[U'/R|_{U'}]^pre → [U/R]^pre` induced by the restriction of a groupoid along
`g : U' → U`: it sends a point of `U'` to its image in `U` and a restricted relation to
its underlying relation. -/
def restrictQuotientMap : (𝒢.restrict g).quotientPrestack ⥤ᵇ 𝒢.quotientPrestack where
  toFunctor :=
    { obj := fun a ↦ ⟨a.base, g.app (op a.base) a.pt⟩
      map := fun {a b} φ ↦
        ⟨φ.hom, φ.rel.1.2, by
          rw [φ.rel.2.1]
          exact congrArg (g.app (op a.base)) φ.s_rel, by
          have ht : φ.rel.1.1.2 = U'.map φ.hom.op b.pt := φ.t_rel
          rw [φ.rel.2.2, ht, NatTrans.naturality_apply]⟩
      map_id := fun a ↦ QuotientHom.ext rfl rfl
      map_comp := fun {a b c} φ ψ ↦ QuotientHom.ext rfl rfl }
  w := rfl

/-- The morphism of quotient prestacks induced by restricting a groupoid is full: a
relation between the images of two restricted objects already carries the source and
target equations required to be a relation in the restricted groupoid. -/
instance restrictQuotientMap_full :
    (𝒢.restrictQuotientMap g).toFunctor.Full where
  map_surjective {a b} φ := by
    let r' : (𝒢.restrict g).R.obj (op a.base) :=
      ⟨⟨⟨a.pt, U'.map φ.hom.op b.pt⟩, φ.rel⟩,
        φ.s_rel,
        φ.t_rel.trans (NatTrans.naturality_apply g φ.hom.op b.pt).symm⟩
    let ψ : QuotientHom a b := ⟨φ.hom, r', rfl, rfl⟩
    refine ⟨ψ, ?_⟩
    apply QuotientHom.ext
    · rfl
    · rfl

/-- The morphism of quotient prestacks induced by restricting a groupoid is faithful:
its image remembers both the base morphism and the underlying relation. -/
instance restrictQuotientMap_faithful :
    (𝒢.restrictQuotientMap g).toFunctor.Faithful where
  map_injective {a b} φ ψ h := by
    have hhom : φ.hom = ψ.hom := congrArg
      (fun q : QuotientHom ((𝒢.restrictQuotientMap g).obj a)
        ((𝒢.restrictQuotientMap g).obj b) => q.hom) h
    have hrel : φ.rel.1.2 = ψ.rel.1.2 := congrArg
      (fun q : QuotientHom ((𝒢.restrictQuotientMap g).obj a)
        ((𝒢.restrictQuotientMap g).obj b) => q.rel) h
    apply QuotientHom.ext
    · exact hhom
    · apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext
        · exact φ.s_rel.trans ψ.s_rel.symm
        · calc
            φ.rel.1.1.2 = U'.map φ.hom.op b.pt := φ.t_rel
            _ = U'.map ψ.hom.op b.pt := by rw [hhom]
            _ = ψ.rel.1.1.2 := ψ.t_rel.symm
      · exact hrel

variable {𝒢} {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
  {𝒳st' : BasedCategory.{v₃, u₃} Scheme.{u}} {i : 𝒢.quotientPrestack ⥤ᵇ 𝒳st}
  {i' : (𝒢.restrict g).quotientPrestack ⥤ᵇ 𝒳st'}

/-- **Exercise 4.4.20** (`exer:slicing-groupoid`) (part (a), inner square): the
restriction `R|_{U'}` is the fiber product of `U' ×_{U, t} R → R` and
`R ×_{s, U} U' → R` (all other squares of the cartesian 3×3 diagram are instances of the
fiber products defining the restriction and of the cartesian square of the presentation,
cf.
`AlgebraicGeometry.PresheafGroupoid.isRepresentedByPresheaf_fiberProduct_of_isStackification`). -/
theorem nonempty_restrict_iso_fiberProduct (g : U' ⟶ 𝒢.U) :
    Nonempty ((𝒢.restrict g).R ≅
      Presheaf.fiberProduct (Presheaf.fiberProduct.snd g 𝒢.t)
        (Presheaf.fiberProduct.fst 𝒢.s g)) := by
  refine ⟨NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun p => ⟨⟨⟨⟨p.1.1.2, p.1.2⟩, p.2.2.symm⟩, ⟨⟨p.1.2, p.1.1.1⟩, p.2.1⟩⟩, rfl⟩
      invFun := fun x => ⟨⟨⟨x.1.2.1.2, x.1.1.1.1⟩, x.1.1.1.2⟩,
        ⟨by
          have hc : x.1.1.1.2 = x.1.2.1.1 := x.2
          rw [hc]; exact x.1.2.2, x.1.1.2.symm⟩⟩
      left_inv := fun p => rfl
      right_inv := fun x => by
        obtain ⟨⟨⟨⟨b, r⟩, h₁⟩, ⟨⟨r', a⟩, h₂⟩⟩, hc⟩ := x
        obtain rfl : r = r' := hc
        rfl }) ?_⟩
  intro T T' f
  rfl

/-- Supporting fiber-product presentation for Exercise 4.4.20: `R|_{U'}` is the fiber
product `(U' ×_{U, t} R) ×_{s ∘ pr₂, U, g} U'`, arranged so that the second
projection is the source of the restricted groupoid. -/
def restrictRIsoS : (𝒢.restrict g).R ≅
    Presheaf.fiberProduct (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g := by
  refine NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun p => ⟨⟨⟨⟨p.1.1.2, p.1.2⟩, p.2.2.symm⟩, p.1.1.1⟩, p.2.1⟩
      invFun := fun x => ⟨⟨⟨x.1.2, x.1.1.1.1⟩, x.1.1.1.2⟩, ⟨x.2, x.1.1.2.symm⟩⟩
      left_inv := fun p => rfl
      right_inv := fun x => rfl }) ?_
  intro T T' f
  rfl

lemma restrictRIsoS_hom_snd :
    (restrictRIsoS g).hom ≫ Presheaf.fiberProduct.snd
      (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g = (𝒢.restrict g).s := rfl

/-- Supporting fiber-product presentation for Exercise 4.4.20: the same fiber product,
arranged through the groupoid inverse so that the second projection is the target
of the restricted groupoid. -/
def restrictRIsoT : (𝒢.restrict g).R ≅
    Presheaf.fiberProduct (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g := by
  refine NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun p => ⟨⟨⟨⟨p.1.1.1, 𝒢.inv.app T p.1.2⟩, by simp [p.2.1]⟩, p.1.1.2⟩,
        by simpa using p.2.2⟩
      invFun := fun x => ⟨⟨⟨x.1.1.1.1, x.1.2⟩, 𝒢.inv.app T x.1.1.1.2⟩,
        by simpa using x.1.1.2.symm, by simpa using x.2⟩
      left_inv := fun p => by
        refine Subtype.ext (Prod.ext rfl ?_)
        exact inv_inv_app 𝒢 p.1.2
      right_inv := fun x => by
        refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl ?_)) rfl)
        exact inv_inv_app 𝒢 x.1.1.1.2 }) ?_
  intro T T' f
  ext p
  refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl ?_)) rfl)
  exact (𝒢.map_inv_app f p.1.2).symm

lemma restrictRIsoT_hom_snd :
    (restrictRIsoT g).hom ≫ Presheaf.fiberProduct.snd
      (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g = (𝒢.restrict g).t := rfl

/-- **Exercise 4.4.20** (`exer:slicing-groupoid`) (part (2), étale case; the book numbers
the parts (a), (2), (3), (4) — see this folder's COMMENTARY.md): if the composition
`U' ×_{U, t} R → R → U` of the second projection with the source is representable by
schemes and étale, then the restriction `R|_{U'} ⇉ U'` is an étale groupoid. -/
theorem restrict_isEtale (g : U' ⟶ 𝒢.U) [𝒢.IsEtale]
    (h : MorphismProperty.presheaf (@Etale : MorphismProperty Scheme.{u})
      (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s)) :
    (𝒢.restrict g).IsEtale := by
  have hsq : IsPullback
      (Presheaf.fiberProduct.fst (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g)
      (Presheaf.fiberProduct.snd (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g)
      (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g :=
    IsPullback.of_isLimit (Presheaf.fiberProduct.isLimit _ _)
  have hsnd : MorphismProperty.presheaf (@Etale : MorphismProperty Scheme.{u})
      (Presheaf.fiberProduct.snd (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (@Etale : MorphismProperty Scheme.{u})).of_isPullback hsq h
  constructor
  · rw [← restrictRIsoS_hom_snd g]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 hsnd
  · rw [← restrictRIsoT_hom_snd g]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 hsnd

/-- **Exercise 4.4.20** (`exer:slicing-groupoid`) (part (2), smooth case): if the
composition `U' ×_{U, t} R → R → U` of the second projection with the source is
representable by schemes and smooth, then the restriction `R|_{U'} ⇉ U'` is a smooth
groupoid. -/
theorem restrict_isSmooth (g : U' ⟶ 𝒢.U) [𝒢.IsSmooth]
    (h : MorphismProperty.presheaf (@Smooth : MorphismProperty Scheme.{u})
      (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s)) :
    (𝒢.restrict g).IsSmooth := by
  have hsq : IsPullback
      (Presheaf.fiberProduct.fst (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g)
      (Presheaf.fiberProduct.snd (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g)
      (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g :=
    IsPullback.of_isLimit (Presheaf.fiberProduct.isLimit _ _)
  have hsnd : MorphismProperty.presheaf (@Smooth : MorphismProperty Scheme.{u})
      (Presheaf.fiberProduct.snd (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s) g) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (@Smooth : MorphismProperty Scheme.{u})).of_isPullback hsq h
  constructor
  · rw [← restrictRIsoS_hom_snd g]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 hsnd
  · rw [← restrictRIsoT_hom_snd g]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 hsnd

/-- **Exercise 4.4.20** (`exer:slicing-groupoid`) (part (3)): let `R ⇉ U` be a smooth
groupoid of algebraic spaces, `g : U' → U` a morphism with `U' ×_{U, t} R → R → U`
smooth, and let `i`, `i'` be stackifications of `[U/R]^pre` and `[U'/R|_{U'}]^pre`. Then
any morphism `j` filling the square of quotient stacks (2-isomorphically compatible with
the induced morphism of quotient prestacks) is an open substack inclusion
`[U'/R|_{U'}] → [U/R]`. -/
theorem isOpenSubstackInclusion_of_restrict [𝒢.IsSmooth] [IsAlgebraicSpace 𝒢.U]
    [IsAlgebraicSpace 𝒢.R]
    (h : MorphismProperty.presheaf (@Smooth : MorphismProperty Scheme.{u})
      (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s))
    (hi : i.IsStackification Scheme.etaleTopology)
    (hi' : i'.IsStackification Scheme.etaleTopology) (j : 𝒳st' ⥤ᵇ 𝒳st)
    (hj : Nonempty (i'.comp j ≅ (𝒢.restrictQuotientMap g).comp i)) :
    BasedFunctor.IsOpenSubstackInclusion j := by
  let _ : 𝒳st.p.IsFiberedInGroupoids := hi.isStack.isFiberedInGroupoids
  let _ : 𝒳st'.p.IsFiberedInGroupoids := hi'.isStack.isFiberedInGroupoids
  have hrel : j.RelativelyRepresentableWith
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) := by
    sorry
  have hmono : j.RelativelyRepresentableWith
      (MorphismProperty.monomorphisms Scheme.{u}) :=
    hrel.mono (fun _ _ f hf => by
      let _ : IsOpenImmersion f := hf
      infer_instance)
  exact
    { full := hmono.toFunctor_full_of_monomorphisms
      faithful := hrel.relativelyRepresentable.toFunctor_faithful
      relativelyRepresentableWith := hrel }

/-- **Exercise 4.4.20** (`exer:slicing-groupoid`) (part (4)): in the situation of part
(3), the morphism `[U'/R|_{U'}] → [U/R]` is an isomorphism (an equivalence) if and only
if every field-valued point of `U` admits, after a field extension, a relation in `R` to
a point in the image of `U'`. (The book phrases the criterion with points `u ∈ U`,
`u' ∈ U`, and a relation `u → g(u')`; the formalization reads points as field-valued and
allows a field extension, and reads `u' ∈ U'` — see this folder's COMMENTARY.md.) -/
theorem restrict_isEquivalence_iff [𝒢.IsSmooth] [IsAlgebraicSpace 𝒢.U]
    [IsAlgebraicSpace 𝒢.R]
    (h : MorphismProperty.presheaf (@Smooth : MorphismProperty Scheme.{u})
      (Presheaf.fiberProduct.snd g 𝒢.t ≫ 𝒢.s))
    (hi : i.IsStackification Scheme.etaleTopology)
    (hi' : i'.IsStackification Scheme.etaleTopology) (j : 𝒳st' ⥤ᵇ 𝒳st)
    (hj : Nonempty (i'.comp j ≅ (𝒢.restrictQuotientMap g).comp i)) :
    j.toFunctor.IsEquivalence ↔
      ∀ (K : Type u) (_ : Field K)
        (x : 𝒢.U.obj (op (Spec (CommRingCat.of K)))),
        ∃ (L : Type u) (_ : Field L)
          (φ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
          (u' : U'.obj (op (Spec (CommRingCat.of L))))
          (r : 𝒢.R.obj (op (Spec (CommRingCat.of L)))),
          𝒢.s.app _ r = 𝒢.U.map φ.op x ∧ 𝒢.t.app _ r = g.app _ u' := by
  let _ : 𝒳st.p.IsFiberedInGroupoids := hi.isStack.isFiberedInGroupoids
  let _ : 𝒳st'.p.IsFiberedInGroupoids := hi'.isStack.isFiberedInGroupoids
  let _ : BasedFunctor.IsOpenSubstackInclusion j :=
    isOpenSubstackInclusion_of_restrict (𝒢 := 𝒢) g h hi hi' j hj
  rw [BasedFunctor.isEquivalence_iff_surjective_mapPoints_of_isOpenSubstackInclusion]
  sorry

end AlgebraicGeometry.PresheafGroupoid

end ExerSlicingGroupoid

section ExerStackOfEllipticCurvesIsFiniteQuotient

/- Unformalized Exercise 4.4.21 (Moduli of elliptic curves revisited): slicing the
presentation
`𝔸² ∖ V(Δ) → 𝓜₁,₁ ≅ [(𝔸² ∖ V(Δ))/𝔾ₘ]` along the closed immersion
`V(Δ - 1) ↪ 𝔸² ∖ V(Δ)` exhibits the moduli stack of elliptic curves (over a field of
characteristic different from `2, 3`) as a quotient `[V(Δ-1)/μ₁₂]` of an affine scheme by
a finite group. It depends on the identification `𝓜₁,₁ ≅ [(𝔸² ∖ V(Δ))/𝔾ₘ]` (Exercise
4.1.21, `exer:stack-of-elliptic-curves-is-algebraic`, deferred in §4.1 together with the
quotient-stack machinery) and on the `μ₁₂`-action on `V(Δ - 1)`. -/

end ExerStackOfEllipticCurvesIsFiniteQuotient
