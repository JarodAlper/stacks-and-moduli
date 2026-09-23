module

public import StacksAndModuli.API.SheafFlatteningImmersion

/-!
# Intersections of flattening loci

The fibre of the Quot-to-Grassmannian map over a point of `Gr` is the locus in the base where
the reconstructed family `Q_E` is flat with the prescribed Hilbert polynomial — equivalently,
where `π_*(Q_E(d'))` is locally free of the prescribed rank for each `d'` in a bounded range.
That is a **finite intersection of flattening loci**, and this file supplies the binary case,
from which the finite case follows by iteration.

Both properties needed downstream survive the intersection for structural reasons: the
structure map of the fibre product is a composite of a base change of an immersion with an
immersion, and likewise for monomorphisms.  Representability is equally cheap because the
flattening functor is subsingleton-valued — the intersection functor is the conjunction, and
injectivity of `homEquiv` is just `cancel_mono`.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.flatRankInter` and its `IsImmersion` / `Mono` instances;
* `AlgebraicGeometry.Scheme.Modules.flatRankInterFunctor` and
  `…flatRankInterRepresentableBy`;
* `AlgebraicGeometry.Scheme.interOver`, `…prodFunctor` and `…interOverRepresentableBy` — the
  same for two arbitrary subfunctors of the terminal presheaf, which is the reusable form;
* `AlgebraicGeometry.Scheme.interOverFin`, `…interOverFin_isImmersion`, `…interOverFin_mono`
  — the finite family, by induction, which is what a Hilbert-polynomial condition (finitely
  many degrees) needs.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The fibre product of two objects over `X` with immersion structure maps again has an
immersion structure map. -/
instance isImmersion_pullbackOver (A B : Over X) [IsImmersion A.hom] [IsImmersion B.hom] :
    IsImmersion (Limits.pullback.fst A.hom B.hom ≫ A.hom) :=
  inferInstance

/-- **The intersection of two flattening loci**, as an object over `X`. -/
def flatRankInter (E₁ E₂ : X.Modules) (r₁ r₂ : ℕ)
    (h₁ : HasChartComparison E₁ r₁) (h₂ : HasChartComparison E₂ r₂) : Over X :=
  Over.mk (Limits.pullback.fst (flatRankRepresentativeOver E₁ r₁ h₁).hom
      (flatRankRepresentativeOver E₂ r₂ h₂).hom ≫
    (flatRankRepresentativeOver E₁ r₁ h₁).hom)

/-- **The intersection of two flattening loci is an immersion into the base.** -/
instance flatRankInter_hom_isImmersion (E₁ E₂ : X.Modules) (r₁ r₂ : ℕ)
    (h₁ : HasChartComparison E₁ r₁) (h₂ : HasChartComparison E₂ r₂) :
    IsImmersion (flatRankInter E₁ E₂ r₁ r₂ h₁ h₂).hom := by
  haveI := flatRankRepresentativeOver_hom_isImmersion E₁ r₁ h₁
  haveI := flatRankRepresentativeOver_hom_isImmersion E₂ r₂ h₂
  exact isImmersion_pullbackOver _ _

/-- The intersection of two flattening loci is a subscheme of the base. -/
instance flatRankInter_hom_mono (E₁ E₂ : X.Modules) (r₁ r₂ : ℕ)
    (h₁ : HasChartComparison E₁ r₁) (h₂ : HasChartComparison E₂ r₂) :
    Mono (flatRankInter E₁ E₂ r₁ r₂ h₁ h₂).hom := by
  haveI : Mono (flatRankRepresentativeOver E₁ r₁ h₁).hom := inferInstance
  haveI : Mono (flatRankRepresentativeOver E₂ r₂ h₂).hom := inferInstance
  change Mono (Limits.pullback.fst _ _ ≫ _)
  infer_instance

/-- The conjunction of two flattening conditions. -/
def flatRankInterFunctor (E₁ E₂ : X.Modules) (r₁ r₂ : ℕ) : (Over X)ᵒᵖ ⥤ Type u where
  obj T := ULift.{u} (PLift (Scheme.LocallyFactors (affineStratum E₁ r₁) T.unop ∧
    Scheme.LocallyFactors (affineStratum E₂ r₂) T.unop))
  map φ := ↾fun h => ⟨⟨Scheme.LocallyFactors.comp φ.unop h.down.down.1,
    Scheme.LocallyFactors.comp φ.unop h.down.down.2⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance flatRankInterFunctor_subsingleton (E₁ E₂ : X.Modules) (r₁ r₂ : ℕ)
    (T : (Over X)ᵒᵖ) : Subsingleton ((flatRankInterFunctor E₁ E₂ r₁ r₂).obj T) := by
  refine ⟨fun a b => ?_⟩
  have ha : a = (⟨⟨a.down.down⟩⟩ : ULift.{u} (PLift _)) := rfl
  have hb : b = (⟨⟨b.down.down⟩⟩ : ULift.{u} (PLift _)) := rfl
  rw [ha, hb]

/-- **The conjunction is represented by the intersection.** -/
def flatRankInterRepresentableBy (E₁ E₂ : X.Modules) (r₁ r₂ : ℕ)
    (h₁ : HasChartComparison E₁ r₁) (h₂ : HasChartComparison E₂ r₂) :
    (flatRankInterFunctor E₁ E₂ r₁ r₂).RepresentableBy
      (flatRankInter E₁ E₂ r₁ r₂ h₁ h₂) where
  homEquiv {T} := by
    refine Equiv.ofBijective (fun f => ⟨⟨
      ((flatRankRepresentableByOver E₁ r₁ h₁).homEquiv
        (Over.homMk (f.left ≫ Limits.pullback.fst _ _) (by
          rw [Category.assoc]
          exact Over.w f) : T ⟶ flatRankRepresentativeOver E₁ r₁ h₁)).down.down,
      ((flatRankRepresentableByOver E₂ r₂ h₂).homEquiv
        (Over.homMk (f.left ≫ Limits.pullback.snd _ _) (by
          rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc]
          exact Over.w f) : T ⟶ flatRankRepresentativeOver E₂ r₂ h₂)).down.down⟩⟩) ?_
    constructor
    · intro a b _
      haveI := flatRankInter_hom_mono E₁ E₂ r₁ r₂ h₁ h₂
      apply Over.OverMorphism.ext
      rw [← cancel_mono (flatRankInter E₁ E₂ r₁ r₂ h₁ h₂).hom, Over.w, Over.w]
    · rintro ⟨⟨h⟩⟩
      refine ⟨Over.homMk (Limits.pullback.lift
        ((flatRankRepresentableByOver E₁ r₁ h₁).homEquiv.symm ⟨⟨h.1⟩⟩).left
        ((flatRankRepresentableByOver E₂ r₂ h₂).homEquiv.symm ⟨⟨h.2⟩⟩).left
        (by rw [Over.w, Over.w])) ?_, Subsingleton.elim _ _⟩
      change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ ≫ _ = T.hom
      rw [← Category.assoc, Limits.pullback.lift_fst, Over.w]
  homEquiv_comp {T T'} g f := Subsingleton.elim _ _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The intersection of two objects over `X`: their fibre product, regarded over `X`. -/
def interOver (A B : Over X) : Over X :=
  Over.mk (Limits.pullback.fst A.hom B.hom ≫ A.hom)

instance interOver_isImmersion (A B : Over X) [IsImmersion A.hom] [IsImmersion B.hom] :
    IsImmersion (interOver A B).hom :=
  inferInstanceAs (IsImmersion (Limits.pullback.fst A.hom B.hom ≫ A.hom))

instance interOver_mono (A B : Over X) [Mono A.hom] [Mono B.hom] :
    Mono (interOver A B).hom :=
  inferInstanceAs (Mono (Limits.pullback.fst A.hom B.hom ≫ A.hom))

/-- The pointwise product of two presheaves of types. -/
def prodFunctor (F G : (Over X)ᵒᵖ ⥤ Type u) : (Over X)ᵒᵖ ⥤ Type u where
  obj T := F.obj T × G.obj T
  map φ := ↾fun p => (F.map φ p.1, G.map φ p.2)
  map_id T := by ext p <;> simp
  map_comp φ ψ := by ext p <;> simp

/-- **The intersection represents the conjunction.**  Both functors are assumed
subsingleton-valued, which is the case for every subfunctor of the terminal presheaf. -/
def interOverRepresentableBy {F G : (Over X)ᵒᵖ ⥤ Type u} {A B : Over X}
    (hF : F.RepresentableBy A) (hG : G.RepresentableBy B)
    (hFs : ∀ T, Subsingleton (F.obj T)) (hGs : ∀ T, Subsingleton (G.obj T))
    [Mono A.hom] [Mono B.hom] :
    (prodFunctor F G).RepresentableBy (interOver A B) where
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

/-- The intersection of a finite family of objects over `X`. -/
def interOverFin : ∀ {k : ℕ}, (Fin k → Over X) → Over X
  | 0, _ => Over.mk (𝟙 X)
  | (_ + 1), A => interOver (A 0) (interOverFin (fun i => A i.succ))

theorem interOverFin_isImmersion :
    ∀ {k : ℕ} (A : Fin k → Over X), (∀ i, IsImmersion (A i).hom) →
      IsImmersion (interOverFin A).hom
  | 0, _, _ => by
    change IsImmersion (𝟙 X)
    infer_instance
  | (_ + 1), A, h => by
    haveI := h 0
    haveI := interOverFin_isImmersion (fun i => A i.succ) (fun i => h i.succ)
    exact interOver_isImmersion _ _

theorem interOverFin_mono :
    ∀ {k : ℕ} (A : Fin k → Over X), (∀ i, Mono (A i).hom) → Mono (interOverFin A).hom
  | 0, _, _ => by
    change Mono (𝟙 X)
    infer_instance
  | (_ + 1), A, h => by
    haveI := h 0
    haveI := interOverFin_mono (fun i => A i.succ) (fun i => h i.succ)
    exact interOver_mono _ _

end AlgebraicGeometry.Scheme
