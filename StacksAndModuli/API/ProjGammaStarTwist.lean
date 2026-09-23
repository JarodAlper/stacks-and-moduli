module

public import StacksAndModuli.API.ProjGammaStarStructure
public import StacksAndModuli.API.ProjectiveTwistMultiplication

/-!
# `Γ_*(𝒪(a)) ≅ S(a)` on `ℙⁿ_k`

The comparison `S ≅ Γ_*(𝒪)` of `API/ProjGammaStarStructure.lean` is extended to the twists:
for `n ≥ 1` and any `a : ℤ`,

`(structureModule k n).twist a ≅ Γ_*(𝒪(a))`.

Together with `GradedModule.IsFG.twist` and `IsFlat.twist` this is what makes the twisted-free
ambient sheaf of a Quot presentation coherent and flat as a graded module.

Two things had to be supplied.

* **The multiplication `𝒪(a) ⊗ 𝒪(d) ≅ 𝒪(a+d)` commutes with multiplication by a form**
  (`ProjectiveSpectrum.Twist.multiplyHom_mulHom`).  At the presheaf level this is
  associativity of `mulSections`, one `ring` call; the passage to sheaves is the sheafification
  adjunction, and the workable route is to rewrite `multiplyHom` as
  `sheafification.map (multiplyPresheafHom) ≫ counit` (`multiplyHom_eq`) and then use
  naturality of the counit.  Trying instead to move the square across
  `Adjunction.homEquiv_naturality_right_symm` times out: the right adjoint is
  `forget ⋙ restrictScalars (𝟙 _)`, and unifying `R.map ψ` with `ψ.val` is expensive.
* **The `eqToHom` in `GradedModule.twist`.**  `(M.twist a).mulX i d` is `M.mulX' i (d+a)
  (d+1+a)`, i.e. `mulX` followed by a transport across `d + a + 1 = d + 1 + a`.  Rather than
  compute the transport, `coe_twist_structureModule_mulX` records that it does not change the
  underlying polynomial, and `mulSectionHom_polyToTwistSections` takes the target form as a
  parameter constrained only by that polynomial.

Main declarations:

* `ProjectiveSpectrum.Twist.multiplyHom_eq`, `multiplyPresheafHom_mulHom`, `multiplyHom_mulHom`;
* `AlgebraicGeometry.ProjectiveSpace.coe_twist_structureModule_mulX`;
* `AlgebraicGeometry.ProjectiveSpace.twistToGammaStar` and
  `AlgebraicGeometry.ProjectiveSpace.twistIsoGammaStar`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry

universe u

namespace ProjectiveSpectrum.Twist

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- `multiplyHom` written through the counit of the sheafification adjunction.  This is the
form in which it can be composed with `sheafification.map` on the left. -/
theorem multiplyHom_eq (u v : ℤ) : multiplyHom 𝒜 u v
    = (Scheme.Modules.sheafification (Proj 𝒜)).map (multiplyPresheafHom 𝒜 u v)
      ≫ (PresheafOfModules.sheafificationAdjunction
          (𝟙 (Proj 𝒜).ringCatSheaf.obj)).counit.app (twist 𝒜 (u + v)) := by
  have h : multiplyHom 𝒜 u v
    = ((PresheafOfModules.sheafificationAdjunction (𝟙 (Proj 𝒜).ringCatSheaf.obj)).homEquiv
        (MonoidalCategoryStruct.tensorObj (C := (Proj 𝒜).PresheafOfModules)
          (twist 𝒜 u).val (twist 𝒜 v).val) (twist 𝒜 (u + v))).symm
        (multiplyPresheafHom 𝒜 u v) := rfl
  rw [h, Adjunction.homEquiv_counit]
  rfl

/-- **Presheaf-level associativity**: multiplying the right factor by a form and then
multiplying the factors is multiplying the factors and then by the form. -/
theorem multiplyPresheafHom_mulHom {m : ℕ} (c : 𝒜 m) (a d dc : ℤ) (hdc : dc = d + (m : ℤ))
    (hadc : a + dc = (a + d) + (m : ℤ)) :
    MonoidalCategoryStruct.whiskerLeft (C := (Proj 𝒜).PresheafOfModules)
        (twist 𝒜 a).val (mulHom 𝒜 c d dc hdc).val ≫ multiplyPresheafHom 𝒜 a dc
      = multiplyPresheafHom 𝒜 a d ≫ (mulHom 𝒜 c (a + d) (a + dc) hadc).val := by
  refine PresheafOfModules.hom_ext (fun U ↦ ?_)
  refine ModuleCat.MonoidalCategory.tensor_ext (fun s t ↦ ?_)
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change (s.1 x).1 * ((t.1 x).1 * Localization.mk (c : A) 1)
    = ((s.1 x).1 * (t.1 x).1) * Localization.mk (c : A) 1
  ring

/-- **Multiplication of twists is compatible with multiplication by a form.**  This is the
square that makes `Γ_*(𝒪(a))` a *graded* module isomorphic to `Γ_*(𝒪)(a)`. -/
theorem multiplyHom_mulHom {m : ℕ} (c : 𝒜 m) (a d dc : ℤ) (hdc : dc = d + (m : ℤ))
    (hadc : a + dc = (a + d) + (m : ℤ)) :
    Scheme.Modules.tensorMapRight (twist 𝒜 a) (mulHom 𝒜 c d dc hdc) ≫ multiplyHom 𝒜 a dc
      = multiplyHom 𝒜 a d ≫ mulHom 𝒜 c (a + d) (a + dc) hadc := by
  rw [multiplyHom_eq, multiplyHom_eq]
  change (Scheme.Modules.sheafification (Proj 𝒜)).map
      (MonoidalCategoryStruct.whiskerLeft (C := (Proj 𝒜).PresheafOfModules)
        (twist 𝒜 a).val (mulHom 𝒜 c d dc hdc).val) ≫ _ = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    multiplyPresheafHom_mulHom 𝒜 c a d dc hdc hadc, CategoryTheory.Functor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)).counit.naturality (mulHom 𝒜 c (a + d) (a + dc) hadc)

end ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

open MvPolynomial ProjectiveSpectrum.Twist

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k] (n : ℕ)

/-- A transport of graded pieces of `S` across an equality of degrees does not change the
underlying polynomial. -/
theorem coe_eqToHom_structureModule {e e' : ℤ} (h : e = e')
    (z : GradedModule.polySubmodule k n e) :
    (((eqToHom (congrArg (GradedModule.structureModule k n).obj h) :
        (GradedModule.structureModule k n).obj e ⟶
          (GradedModule.structureModule k n).obj e').hom z).1
      : MvPolynomial (Fin (n + 1)) k) = z.1 := by
  subst h
  simp

/-- **The degree-raising map of `S(a)` is still multiplication by `xᵢ`**, the `eqToHom` of
`GradedModule.twist` notwithstanding. -/
theorem coe_twist_structureModule_mulX (a : ℤ) (i : Fin (n + 1)) (d : ℤ)
    (p : GradedModule.polySubmodule k n (d + a)) :
    (((((GradedModule.structureModule k n).twist a).mulX i d).hom p).1
        : MvPolynomial (Fin (n + 1)) k)
      = MvPolynomial.X i * (p.1 : MvPolynomial (Fin (n + 1)) k) := by
  rw [GradedModule.twist_mulX]
  exact coe_eqToHom_structureModule k n (show d + a + 1 = d + 1 + a by ring)
    (GradedModule.polyMulX k n i (d + a) p)

/-- **The comparison `S(a) ⟶ Γ_*(𝒪(a))`.**  In degree `d` a form of degree `d + a` becomes
the section `p / 1` of `𝒪(a+d)`, read in `𝒪(a) ⊗ 𝒪(d)` through the multiplication
isomorphism. -/
noncomputable def twistToGammaStar (a : ℤ) :
    (GradedModule.structureModule k n).twist a ⟶
      Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (projπ k n)
        (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) a) (stdVars n k) :=
  letI (d : ℤ) : Module (CommRingCat.of k)
      Γ(twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) a) d, ⊤) :=
    Scheme.Modules.globalSectionsModule (projπ k n)
      (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) a) d)
  letI (e : ℤ) : Module (CommRingCat.of k)
      Γ(twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) e, ⊤) :=
    Scheme.Modules.globalSectionsModule (projπ k n)
      (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) e)
  { app := fun d ↦ ModuleCat.ofHom
      ((Scheme.Modules.globalSectionsLinearMap (projπ k n)
        (polynomialMultiplyIso (R := k) (Fin (n + 1)) a d).inv).comp
        (polyToTwistSections k n (d + a) (a + d) (by ring)))
    comm := fun i d ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun p ↦ ?_)
      have hsq := multiplyHom_mulHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (stdVars n k i) a d (d + 1) (by push_cast; ring) (by push_cast; ring)
      have hinv : (polynomialMultiplyIso (R := k) (Fin (n + 1)) a d).inv ≫
            Scheme.Modules.tensorMapRight
              (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) a)
              (mulHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (stdVars n k i) d
                (d + 1) (by push_cast; ring))
          = mulHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (stdVars n k i) (a + d)
              (a + (d + 1)) (by push_cast; ring) ≫
            (polynomialMultiplyIso (R := k) (Fin (n + 1)) a (d + 1)).inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
        exact hsq
      have happ := congrArg
        (fun ψ : twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (a + d) ⟶
            twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
              (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) a) (d + 1) ↦
          (PresheafOfModules.Hom.app ψ.val (op ⊤)).hom
            (polyToTwistSections k n (d + a) (a + d) (by ring) p)) hinv
      refine happ.trans ?_
      refine congrArg (fun z : Γ(twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
          (a + (d + 1)), ⊤) ↦
        (PresheafOfModules.Hom.app
          (polynomialMultiplyIso (R := k) (Fin (n + 1)) a (d + 1)).inv.val (op ⊤)).hom z) ?_
      exact mulSectionHom_polyToTwistSections k n i (d + a) (a + d) (d + 1 + a) (a + (d + 1))
        (by ring) (by ring) (by ring) p
        ((((GradedModule.structureModule k n).twist a).mulX i d).hom p)
        (coe_twist_structureModule_mulX k n a i d p) }

/-- **`S(a) ≅ Γ_*(𝒪(a))` on `ℙⁿ_k` for `n ≥ 1`.** -/
noncomputable def twistIsoGammaStar (hn : 0 < n) (a : ℤ) :
    (GradedModule.structureModule k n).twist a ≅
      Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (projπ k n)
        (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) a) (stdVars n k) :=
  GradedModule.isoOfBijective (twistToGammaStar k n a) (fun d ↦ by
    have hu := Scheme.Modules.bijective_app_of_iso
      (polynomialMultiplyIso (R := k) (Fin (n + 1)) a d).symm (op ⊤)
    exact hu.comp (bijective_polyToTwistSections k n hn (d + a) (a + d) (by ring)))

end AlgebraicGeometry.ProjectiveSpace

end

end
