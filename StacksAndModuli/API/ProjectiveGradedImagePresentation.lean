module

public import StacksAndModuli.API.ProjectiveGradedSerre
public import StacksAndModuli.API.ProjectiveGradedTotalFinite

/-!
# Finite presentations for the eventual free presentation

The standard one-degree free map onto a finitely generated graded module need only be
surjective in sufficiently large degrees.  Its image, however, is a genuine quotient of a
finite free graded module: it is zero below the generating degree and agrees with the target
above it.  This file records the resulting finiteness and flatness facts and transports finite
presentation of the total image module back to finite generation of the diagrammatic kernel.

This is the bridge which replaces the noetherian submodule argument in relative Serre
finiteness by the graded flat finite-presentation theorem (Stacks Project tag 053C).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {R : Type u} [CommRing R] {n r : ℕ}

/-! ## Finiteness and flatness of the image -/

/-- A degreewise quotient of a finitely generated graded module is finitely generated. -/
lemma IsFG.of_surjective {M N : GradedModule R n} (hM : IsFG M) (f : M ⟶ N)
    (hf : ∀ d : ℤ, Function.Surjective ((f.app d).hom)) : IsFG N := by
  obtain ⟨hfinite, ⟨a, hzero⟩, ⟨b, hgen⟩⟩ := hM
  refine ⟨fun d => ?_, ⟨a, fun d hd => ?_⟩, ⟨b, fun d hd => ?_⟩⟩
  · letI : Module.Finite R (M.obj d) := hfinite d
    exact Module.Finite.of_surjective (f.app d).hom (hf d)
  · letI : Subsingleton (M.obj d) := hzero d hd
    exact Function.Surjective.subsingleton (hf d)
  · exact mulSpan_eq_top_of_surjective f hf d (d + 1) (hgen d hd)

/-- In degrees in which the chosen generators generate, the inclusion of the image of the
free presentation is surjective. -/
lemma surjective_imgIota (M : GradedModule R n) (d₀ : ℤ) (y : Fin r → M.obj d₀)
    (hy : Submodule.span R (Set.range y) = ⊤)
    (hgen : ∀ d : ℤ, d₀ ≤ d → M.mulSpan d (d + 1) = ⊤)
    (d : ℤ) (hd : d₀ ≤ d) :
    Function.Surjective (((imgIota M d₀ y).app d).hom) := by
  intro z
  have hz : z ∈ LinearMap.ker (((toCoker (freeGenHom M d₀ y)).app d).hom) := by
    obtain ⟨p, hp⟩ := surjective_freeGenHom_app M d₀ y hy hgen d hd z
    rw [toCoker_app]
    change (LinearMap.range (((freeGenHom M d₀ y).app d).hom)).mkQ z = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨p, hp⟩
  exact ⟨⟨z, hz⟩, rfl⟩

/-- Below the generating degree, the image of the one-degree free presentation is zero. -/
lemma subsingleton_imgMod_of_lt (M : GradedModule R n) (d₀ : ℤ)
    (y : Fin r → M.obj d₀) (d : ℤ) (hd : d < d₀) :
    Subsingleton ((imgMod M d₀ y).obj d) := by
  have hsource : Subsingleton
      (((((structureModule R n).twist (-d₀)).pow r).obj d)) := by
    have hneg : d + -d₀ < 0 := by omega
    haveI : Subsingleton ((structureModule R n).obj (d + -d₀)) :=
      subsingleton_polySubmodule_lt_zero hneg
    exact inferInstanceAs (Subsingleton (Fin r → (structureModule R n).obj (d + -d₀)))
  exact Function.Surjective.subsingleton (surjective_freeGenToImg M d₀ y d)

/-- The image of the eventual free presentation is flat when the target is degreewise flat. -/
lemma IsFlat.freeGenImage {M : GradedModule R n} (hM : IsFlat M) (d₀ : ℤ)
    (y : Fin r → M.obj d₀) (hy : Submodule.span R (Set.range y) = ⊤)
    (hgen : ∀ d : ℤ, d₀ ≤ d → M.mulSpan d (d + 1) = ⊤) :
    IsFlat (imgMod M d₀ y) := by
  intro d
  rcases lt_or_ge d d₀ with hd | hd
  · letI : Subsingleton ((imgMod M d₀ y).obj d) :=
      subsingleton_imgMod_of_lt M d₀ y d hd
    exact Module.Flat.of_retract (0 : (imgMod M d₀ y).obj d →ₗ[R] R)
      (0 : R →ₗ[R] (imgMod M d₀ y).obj d)
      (LinearMap.ext fun x => Subsingleton.elim _ _)
  · letI : Module.Flat R (M.obj d) := hM d
    let e : (imgMod M d₀ y).obj d ≃ₗ[R] M.obj d :=
      LinearEquiv.ofBijective ((imgIota M d₀ y).app d).hom
        ⟨injective_imgIota M d₀ y d, surjective_imgIota M d₀ y hy hgen d hd⟩
    exact Module.Flat.of_linearEquiv e

/-- The image of the eventual free presentation is finitely generated, without any
noetherian hypothesis. -/
lemma isFG_imgMod (M : GradedModule R n) (d₀ : ℤ) (y : Fin r → M.obj d₀) :
    IsFG (imgMod M d₀ y) :=
  (isFG_structureModule.twist (-d₀)).pow r |>.of_surjective
    (freeGenToImg M d₀ y) (surjective_freeGenToImg M d₀ y)

/-! ## Total maps and relation modules -/

namespace Total

/-- A degreewise-surjective graded morphism induces a surjection on total modules. -/
lemma surjective_map_of_surjective {M N : GradedModule R n} (f : M ⟶ N)
    (hf : ∀ d : ℤ, Function.Surjective ((f.app d).hom)) :
    Function.Surjective (map f) := by
  intro z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of d x =>
      obtain ⟨w, rfl⟩ := hf d x
      exact ⟨tof M d w, map_tof f d w⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add (map f) x' y'⟩

/-- Finite presentation of the total target of a degreewise surjection makes the total
degreewise kernel finite. -/
lemma finite_kernel_of_finitePresentation {M N : GradedModule R n} (f : M ⟶ N)
    (hM : IsFG M) (hf : ∀ d : ℤ, Function.Surjective ((f.app d).hom))
    [Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R) (Total N)] :
    Module.Finite (MvPolynomial (Fin (n + 1)) R) (Total (ker f)) := by
  letI : Module.Finite (MvPolynomial (Fin (n + 1)) R) (Total M) := finite_total M hM
  have hker : (LinearMap.ker (map f)).FG :=
    Module.FinitePresentation.fg_ker (map f) (surjective_map_of_surjective f hf)
  letI : Module.Finite (MvPolynomial (Fin (n + 1)) R) (LinearMap.ker (map f)) :=
    Module.Finite.iff_fg.mpr hker
  exact Module.Finite.equiv (kernelLinearEquiv f).symm

/-- A degreewise-surjective map from a finitely generated graded module to a target whose
total module is finitely presented has a finitely generated diagrammatic kernel. -/
lemma isFG_kernel_of_finitePresentation {M N : GradedModule R n} (f : M ⟶ N)
    (hM : IsFG M) (hf : ∀ d : ℤ, Function.Surjective ((f.app d).hom))
    [Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R) (Total N)] :
    IsFG (ker f) := by
  let hfinite : Module.Finite (MvPolynomial (Fin (n + 1)) R) (Total (ker f)) :=
    finite_kernel_of_finitePresentation f hM hf
  exact isFG_of_finite_total (ker f) hfinite

end Total

/-! ## Comparison with the kernel used by Serre dévissage -/

/-- The kernel of the map corestricted to its image maps back to the kernel of the original
free-generator map. -/
noncomputable def freeGenImageKernelToKernel (M : GradedModule R n) (d₀ : ℤ)
    (y : Fin r → M.obj d₀) :
    ker (freeGenToImg M d₀ y) ⟶ ker (freeGenHom M d₀ y) :=
  kerLift (freeGenHom M d₀ y) (kerι (freeGenToImg M d₀ y)) (fun d x => by
    exact congrArg Subtype.val (LinearMap.mem_ker.mp x.2))

/-- The comparison from the kernel of the corestricted map to the original kernel is
degreewise surjective. -/
lemma surjective_freeGenImageKernelToKernel (M : GradedModule R n) (d₀ : ℤ)
    (y : Fin r → M.obj d₀) (d : ℤ) :
    Function.Surjective (((freeGenImageKernelToKernel M d₀ y).app d).hom) := by
  intro z
  let w : (ker (freeGenToImg M d₀ y)).obj d :=
    ⟨z.1, LinearMap.mem_ker.mpr (Subtype.ext (LinearMap.mem_ker.mp z.2))⟩
  exact ⟨w, Subtype.ext rfl⟩

/-- If the total image of the eventual free presentation is finitely presented, then its
diagrammatic relation module is finitely generated. -/
lemma isFG_kernel_freeGenHom_of_finitePresentation_image
    (M : GradedModule R n) (d₀ : ℤ) (y : Fin r → M.obj d₀)
    [Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R)
      (Total (imgMod M d₀ y))] :
    IsFG (ker (freeGenHom M d₀ y)) := by
  have hK : IsFG (ker (freeGenToImg M d₀ y)) :=
    Total.isFG_kernel_of_finitePresentation (freeGenToImg M d₀ y)
      ((isFG_structureModule.twist (-d₀)).pow r)
      (surjective_freeGenToImg M d₀ y)
  exact hK.of_surjective (freeGenImageKernelToKernel M d₀ y)
    (surjective_freeGenImageKernelToKernel M d₀ y)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
