module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»
public import Mathlib.Algebra.DualNumber

/-!
# Tangent spaces of algebraic stacks

This module formalizes **Definition 4.5.7** (`def:tangent-space`) and
**Proposition 4.5.10** (`prop:tangent-space`) of §4.5 (Dimension,
tangent spaces, and residual gerbes) of *Stacks and Moduli*
(this section carries no `sec:` label).
**Example 4.5.8** (`ex:mg-tangent-space`), **Example 4.5.9** (`ex:bunC-tangent-space`),
and the unlabeled hard exercise after `prop:tangent-space` are deferred; see the ledger
comments in their sections and this folder's STATUS.md.

For a prestack `𝒳` over `Sch`, a field `k` and a point `x : 𝒳(Spec k)` (an object of the
fiber of `𝒳` over `Spec k`, which by the 2-Yoneda lemma is a morphism `Spec k → 𝒳`), a
tangent vector is an extension of `x` to the dual numbers: an object `τ` of `𝒳` over
`Spec k[ε]` together with a morphism `x ⟶ τ` lying over `Spec k → Spec k[ε]`. Since `𝒳`
is fibered in groupoids this datum is equivalent to the book's 2-commutative diagram
`(τ, α)`. The tangent space is the quotient by the evident equivalence.

Main results:
- `AlgebraicGeometry.BasedCategory.TangentVector` and
  `AlgebraicGeometry.BasedCategory.TangentSpace`: tangent vectors and the tangent space
  `T_{𝒳,x}`.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefTangentSpace

open CategoryTheory Functor CategoryTheory.Functor.IsPreFibered DualNumber

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Functor.IsFibered

variable {𝒮 : Type u₁} {𝒴 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒴]
  (p : 𝒴 ⥤ 𝒮) [p.IsFibered] {R S : 𝒮} (f : R ⟶ S)

/-- Let `p : 𝒴 ⥤ 𝒮` be a fibered category and `f : R ⟶ S`. For a morphism `ψ : a ⟶ b` of
the fiber of `p` over `S`, the composition of the chosen pullback morphism
`f^*a ⟶ a` with `ψ` lies over `f`. -/
lemma isHomLift_pullbackMap_comp_fiberInclusion_map {a b : p.Fiber S} (ψ : a ⟶ b) :
    IsHomLift p f (pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ) := by
  have h₁ := IsHomLift.comp p f (𝟙 S) (pullbackMap a.2 f) (Fiber.fiberInclusion.map ψ)
  simpa using h₁

/-- Let `p : 𝒴 ⥤ 𝒮` be a fibered category and `f : R ⟶ S`. The morphism `f^*a ⟶ f^*b`
between the chosen pullbacks induced by a morphism `ψ : a ⟶ b` of the fiber of `p` over
`S`, obtained from the universal property of the strongly cartesian morphism
`f^*b ⟶ b`. -/
noncomputable def pullbackFunctorMap {a b : p.Fiber S} (ψ : a ⟶ b) :
    pullbackObj a.2 f ⟶ pullbackObj b.2 f :=
  have h := isHomLift_pullbackMap_comp_fiberInclusion_map p f ψ
  IsStronglyCartesian.map p f (pullbackMap b.2 f) (show f = 𝟙 R ≫ f by simp)
    (pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ)

/-- The induced morphism on pullbacks lies over the identity. -/
lemma pullbackFunctorMap_isHomLift {a b : p.Fiber S} (ψ : a ⟶ b) :
    IsHomLift p (𝟙 R) (pullbackFunctorMap p f ψ) := by
  have h := isHomLift_pullbackMap_comp_fiberInclusion_map p f ψ
  exact IsStronglyCartesian.map_isHomLift p f (pullbackMap b.2 f)
    (show f = 𝟙 R ≫ f by simp) (pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ)

/-- The induced morphism on pullbacks commutes with the chosen pullback morphisms. -/
@[reassoc (attr := simp)]
lemma pullbackFunctorMap_fac {a b : p.Fiber S} (ψ : a ⟶ b) :
    pullbackFunctorMap p f ψ ≫ pullbackMap b.2 f =
      pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ := by
  have h := isHomLift_pullbackMap_comp_fiberInclusion_map p f ψ
  exact IsStronglyCartesian.fac p f (pullbackMap b.2 f)
    (show f = 𝟙 R ≫ f by simp) (pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ)

/-- Uniqueness of the induced morphism on pullbacks: any morphism `f^*a ⟶ f^*b` over the
identity commuting with the chosen pullback morphisms is the induced one. -/
lemma pullbackFunctorMap_uniq {a b : p.Fiber S} (ψ : a ⟶ b)
    (χ : pullbackObj a.2 f ⟶ pullbackObj b.2 f) [IsHomLift p (𝟙 R) χ]
    (hχ : χ ≫ pullbackMap b.2 f = pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ) :
    χ = pullbackFunctorMap p f ψ := by
  have h := isHomLift_pullbackMap_comp_fiberInclusion_map p f ψ
  exact IsStronglyCartesian.map_uniq p f (pullbackMap b.2 f)
    (show f = 𝟙 R ≫ f by simp) (pullbackMap a.2 f ≫ Fiber.fiberInclusion.map ψ) χ hχ

/-- The induced morphism on pullbacks of an identity is the identity. -/
@[simp]
lemma pullbackFunctorMap_id (a : p.Fiber S) :
    pullbackFunctorMap p f (𝟙 a) = 𝟙 (pullbackObj a.2 f) := by
  have h : IsHomLift p (𝟙 R) (𝟙 (pullbackObj a.2 f)) :=
    IsHomLift.id (pullbackObj_proj a.2 f)
  refine (pullbackFunctorMap_uniq p f (𝟙 a) (𝟙 _) ?_).symm
  simp only [Category.id_comp, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- The induced morphism on pullbacks of a composition is the composition of the induced
morphisms. -/
@[simp]
lemma pullbackFunctorMap_comp {a b c : p.Fiber S} (ψ : a ⟶ b) (χ : b ⟶ c) :
    pullbackFunctorMap p f (ψ ≫ χ) =
      pullbackFunctorMap p f ψ ≫ pullbackFunctorMap p f χ := by
  have h : IsHomLift p (𝟙 R) (pullbackFunctorMap p f ψ ≫ pullbackFunctorMap p f χ) := by
    have h₁ := pullbackFunctorMap_isHomLift p f ψ
    have h₂ := pullbackFunctorMap_isHomLift p f χ
    have h₃ := IsHomLift.comp p (𝟙 R) (𝟙 R) (pullbackFunctorMap p f ψ)
      (pullbackFunctorMap p f χ)
    simpa using h₃
  refine (pullbackFunctorMap_uniq p f (ψ ≫ χ) _ ?_).symm
  simp [Functor.map_comp]

/-- Let `p : 𝒴 ⥤ 𝒮` be a fibered category and `f : R ⟶ S`. The pullback functor
`f^* : 𝒴(S) ⥤ 𝒴(R)` between fiber categories given by a choice of cartesian pullbacks
along `f`. -/
noncomputable def pullbackFunctor : p.Fiber S ⥤ p.Fiber R where
  obj a := Fiber.mk (pullbackObj_proj a.2 f)
  map {a b} ψ := ⟨pullbackFunctorMap p f ψ, pullbackFunctorMap_isHomLift p f ψ⟩
  map_id a := by
    apply Fiber.hom_ext
    change pullbackFunctorMap p f (𝟙 a) = 𝟙 (pullbackObj a.2 f)
    simp
  map_comp {a b c} ψ χ := by
    apply Fiber.hom_ext
    change pullbackFunctorMap p f (ψ ≫ χ) =
      pullbackFunctorMap p f ψ ≫ pullbackFunctorMap p f χ
    simp

variable {R' : 𝒮} {g : R' ⟶ R} {w : R' ⟶ S}

/-- Let `p : 𝒴 ⥤ 𝒮` be a fibered category, `f : R ⟶ S`, and `w = g ≫ f` a factorization
of a morphism `w : R' ⟶ S`. The transition morphism `w^*a ⟶ f^*a` between the chosen
pullbacks of an object `a` of the fiber over `S`, lying over `g`. -/
noncomputable def pullbackTransition (hw : w = g ≫ f) (a : p.Fiber S) :
    pullbackObj a.2 w ⟶ pullbackObj a.2 f :=
  IsStronglyCartesian.map p f (pullbackMap a.2 f) hw (pullbackMap a.2 w)

/-- The transition morphism between chosen pullbacks lies over the factoring morphism. -/
lemma pullbackTransition_isHomLift (hw : w = g ≫ f) (a : p.Fiber S) :
    IsHomLift p g (pullbackTransition p f hw a) :=
  IsStronglyCartesian.map_isHomLift p f (pullbackMap a.2 f) hw (pullbackMap a.2 w)

/-- The transition morphism commutes with the chosen pullback morphisms. -/
@[reassoc (attr := simp)]
lemma pullbackTransition_fac (hw : w = g ≫ f) (a : p.Fiber S) :
    pullbackTransition p f hw a ≫ pullbackMap a.2 f = pullbackMap a.2 w :=
  IsStronglyCartesian.fac p f (pullbackMap a.2 f) hw (pullbackMap a.2 w)

/-- Naturality of the transition morphisms: they commute with the morphisms induced on
pullbacks by a morphism of the fiber over `S`. -/
lemma pullbackTransition_naturality (hw : w = g ≫ f) {a b : p.Fiber S} (ψ : a ⟶ b) :
    pullbackTransition p f hw a ≫ pullbackFunctorMap p f ψ =
      pullbackFunctorMap p w ψ ≫ pullbackTransition p f hw b := by
  have h₀ := isHomLift_pullbackMap_comp_fiberInclusion_map p w ψ
  have hta := pullbackTransition_isHomLift p f hw a
  have htb := pullbackTransition_isHomLift p f hw b
  have hma := pullbackFunctorMap_isHomLift p f ψ
  have hmw := pullbackFunctorMap_isHomLift p w ψ
  have hL : IsHomLift p g (pullbackTransition p f hw a ≫ pullbackFunctorMap p f ψ) := by
    have h₁ := IsHomLift.comp p g (𝟙 R) (pullbackTransition p f hw a)
      (pullbackFunctorMap p f ψ)
    simpa using h₁
  have hR : IsHomLift p g (pullbackFunctorMap p w ψ ≫ pullbackTransition p f hw b) := by
    have h₁ := IsHomLift.comp p (𝟙 R') g (pullbackFunctorMap p w ψ)
      (pullbackTransition p f hw b)
    simpa using h₁
  have hLu := IsStronglyCartesian.map_uniq p f (pullbackMap b.2 f) hw
    (pullbackMap a.2 w ≫ Fiber.fiberInclusion.map ψ)
    (pullbackTransition p f hw a ≫ pullbackFunctorMap p f ψ) (by simp)
  have hRu := IsStronglyCartesian.map_uniq p f (pullbackMap b.2 f) hw
    (pullbackMap a.2 w ≫ Fiber.fiberInclusion.map ψ)
    (pullbackFunctorMap p w ψ ≫ pullbackTransition p f hw b) (by simp)
  rw [hLu, hRu]

end CategoryTheory.Functor.IsFibered

namespace AlgebraicGeometry

open TrivSqZeroExt

/- Background construction used in Definition 4.5.7: the *dual numbers* over a field
$k$ (more generally, a commutative ring), namely the ring
$k[\epsilon] = k[x]/(x^2)$, realized in Mathlib as `DualNumber k = TrivSqZeroExt k k`
with the square-zero generator `ε`. -/
example (k : Type u) [Field k] : CommRing (DualNumber k) := inferInstance

/-- The closed immersion $\Spec k \to \Spec k[\epsilon]$ induced by the projection
$k[\epsilon] \to k$, $\epsilon \mapsto 0$. -/
noncomputable def specDualNumberInclusion (k : Type u) [Field k] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (fstHom k k k).toRingHom)

/-- Let $R$ be a commutative ring and $c \in R$. The $R$-algebra endomorphism of the dual
numbers $R[\epsilon]$ determined by $\epsilon \mapsto c\epsilon$. -/
def dualNumberSmulHom {R : Type u} [CommRing R] (c : R) :
    DualNumber R →ₐ[R] DualNumber R :=
  DualNumber.lift ⟨(inlAlgHom R R R, c • ε), by
    rw [smul_mul_smul_comm, DualNumber.eps_mul_eps, smul_zero], fun a ↦ Commute.all _ _⟩

/-- The rescaling endomorphism of the dual numbers sends `ε` to `c • ε`. -/
@[simp]
lemma dualNumberSmulHom_eps {R : Type u} [CommRing R] (c : R) :
    dualNumberSmulHom c ε = c • ε :=
  DualNumber.lift_apply_eps _

/-- The rescaling morphism $\Spec k[\epsilon] \to \Spec k[\epsilon]$ induced by
$\epsilon \mapsto c\epsilon$ for a scalar $c \in k$. -/
noncomputable def specDualNumberSmul (k : Type u) [Field k] (c : k) :
    Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (dualNumberSmulHom c).toRingHom)

/-- The composition of the closed immersion $\Spec k \to \Spec k[\epsilon]$ with the
rescaling $\epsilon \mapsto c\epsilon$ is the closed immersion itself. -/
lemma specDualNumberInclusion_comp_specDualNumberSmul (k : Type u) [Field k] (c : k) :
    specDualNumberInclusion k ≫ specDualNumberSmul k c = specDualNumberInclusion k := by
  have h' : (fstHom k k k).comp (dualNumberSmulHom c) = fstHom k k k := by
    apply DualNumber.algHom_ext
    simp
  have h : (fstHom k k k).toRingHom.comp (dualNumberSmulHom c).toRingHom =
      (fstHom k k k).toRingHom :=
    congrArg AlgHom.toRingHom h'
  rw [specDualNumberInclusion, specDualNumberSmul, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h]

end AlgebraicGeometry

namespace AlgebraicGeometry.BasedCategory

open CategoryTheory.Functor.IsFibered

variable {𝒳 : CategoryTheory.BasedCategory.{v₂, u₂} Scheme.{u}} {k : Type u} [Field k]

/-- **Definition 4.5.7** (`def:tangent-space`) (the implicit notion of a tangent vector,
before passing to equivalence classes): let $\cX$ be a prestack over $\Sch$, $k$ a field,
and $x$ an object of $\cX$ over
$\Spec k$ (by the 2-Yoneda lemma, a morphism $x \colon \Spec k \to \cX$). A *tangent
vector* of $\cX$ at $x$: an object $\tau$ of $\cX$ over $\Spec k[\epsilon]$ together with
a morphism $x \to \tau$ of $\cX$ lying over the closed immersion
$\Spec k \to \Spec k[\epsilon]$. Since $\cX$ is fibered in groupoids this datum is
equivalent to the book's pair $(\tau, \alpha)$ of a morphism
$\tau \colon \Spec k[\epsilon] \to \cX$ and a 2-isomorphism
$\alpha \colon x \cong \tau|_{\Spec k}$. -/
structure TangentVector (𝒳 : CategoryTheory.BasedCategory.{v₂, u₂} Scheme.{u})
    {k : Type u} [Field k] (x : 𝒳.p.Fiber (Spec (CommRingCat.of k))) where
  /-- The extension `τ`: an object of the fiber of `𝒳` over `Spec k[ε]`. -/
  pt : 𝒳.p.Fiber (Spec (CommRingCat.of (DualNumber k)))
  /-- The morphism `x ⟶ τ` of `𝒳`. -/
  hom : x.1 ⟶ pt.1
  /-- The morphism `x ⟶ τ` lies over `Spec k → Spec k[ε]`. -/
  isHomLift : IsHomLift 𝒳.p (specDualNumberInclusion k) hom

attribute [instance] TangentVector.isHomLift

namespace TangentVector

variable {x : 𝒳.p.Fiber (Spec (CommRingCat.of k))}

/-- **Definition 4.5.7** (`def:tangent-space`) (the equivalence relation): two tangent
vectors $(\tau, \varphi)$ and $(\tau', \varphi')$ of $\cX$ at $x$ are
*equivalent* if there is a morphism $\beta \colon \tau \to \tau'$ in the fiber of $\cX$
over $\Spec k[\epsilon]$ (automatically an isomorphism) with
$\varphi \circ \beta = \varphi'$; this corresponds to the book's 2-isomorphism
$\beta \colon \tau \cong \tau'$ compatible with $\alpha$ and $\alpha'$. -/
def Equiv (t t' : TangentVector 𝒳 x) : Prop :=
  ∃ β : t.pt ⟶ t'.pt, t.hom ≫ Fiber.fiberInclusion.map β = t'.hom

/-- The equivalence of tangent vectors is reflexive. -/
lemma Equiv.refl (t : TangentVector 𝒳 x) : Equiv t t :=
  ⟨𝟙 t.pt, by
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id t.hom⟩

/-- The equivalence of tangent vectors is symmetric. -/
lemma Equiv.symm [𝒳.p.IsFiberedInGroupoids] {t t' : TangentVector 𝒳 x}
    (h : Equiv t t') : Equiv t' t := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨inv β, ?_⟩
  rw [← hβ, Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id t.hom

/-- The equivalence of tangent vectors is transitive. -/
lemma Equiv.trans {t t' t'' : TangentVector 𝒳 x} (h : Equiv t t') (h' : Equiv t' t'') :
    Equiv t t'' := by
  obtain ⟨β, hβ⟩ := h
  obtain ⟨γ, hγ⟩ := h'
  exact ⟨β ≫ γ, by rw [CategoryTheory.Functor.map_comp, ← Category.assoc, hβ, hγ]⟩

end TangentVector

/-- **Definition 4.5.7** (`def:tangent-space`): let $\cX$ be a prestack over $\Sch$, $k$
a field, and $x$ an object of $\cX$ over
$\Spec k$. The *tangent space* $T_{\cX,x}$ of $\cX$ at $x$: the set of extensions of $x$
to the dual numbers — equivalently, the set of 2-commutative diagrams completing
$x \colon \Spec k \to \cX$ over $\Spec k \hookrightarrow \Spec k[\epsilon]$ — modulo the
equivalence identifying two extensions related by a 2-isomorphism over
$\Spec k[\epsilon]$. -/
def TangentSpace (𝒳 : CategoryTheory.BasedCategory.{v₂, u₂} Scheme.{u}) {k : Type u}
    [Field k] (x : 𝒳.p.Fiber (Spec (CommRingCat.of k))) :=
  Quot (TangentVector.Equiv (𝒳 := 𝒳) (x := x))

namespace TangentSpace

variable {x : 𝒳.p.Fiber (Spec (CommRingCat.of k))}

/-- The tangent space element determined by a tangent vector. -/
def mk (t : TangentVector 𝒳 x) : TangentSpace 𝒳 x :=
  Quot.mk _ t

/-- Equivalent tangent vectors determine the same element of the tangent space. -/
lemma sound {t t' : TangentVector 𝒳 x} (h : TangentVector.Equiv t t') : mk t = mk t' :=
  Quot.sound h

/-- Every element of the tangent space comes from a tangent vector. -/
lemma ind {motive : TangentSpace 𝒳 x → Prop}
    (h : ∀ t : TangentVector 𝒳 x, motive (mk t)) : ∀ v : TangentSpace 𝒳 x, motive v :=
  Quot.ind h

end TangentSpace

namespace TangentVector

variable [𝒳.p.IsFiberedInGroupoids] {x : 𝒳.p.Fiber (Spec (CommRingCat.of k))}

/-- Supporting construction for Proposition 4.5.10: the scalar action of $c \in k$ on a
tangent vector $(\tau, \varphi)$ of $\cX$
at $x$: the pullback of $\tau$ along the rescaling
$\Spec k[\epsilon] \to \Spec k[\epsilon]$,
$\epsilon \mapsto c\epsilon$, with the induced morphism from $x$ (in the book's terms,
the composition $\Spec k[\epsilon] \to \Spec k[\epsilon] \xrightarrow{\tau} \cX$ with the
same 2-isomorphism $\alpha$). -/
noncomputable def smul (c : k) (t : TangentVector 𝒳 x) : TangentVector 𝒳 x where
  pt := Fiber.mk (pullbackObj_proj t.pt.2 (specDualNumberSmul k c))
  hom :=
    IsStronglyCartesian.map 𝒳.p (specDualNumberSmul k c)
      (pullbackMap t.pt.2 (specDualNumberSmul k c))
      (specDualNumberInclusion_comp_specDualNumberSmul k c).symm t.hom
  isHomLift :=
    IsStronglyCartesian.map_isHomLift 𝒳.p (specDualNumberSmul k c)
      (pullbackMap t.pt.2 (specDualNumberSmul k c))
      (specDualNumberInclusion_comp_specDualNumberSmul k c).symm t.hom

/-- The morphism of the scalar multiple of a tangent vector composes with the chosen
pullback morphism to the original morphism. -/
@[reassoc (attr := simp)]
lemma smul_hom_fac (c : k) (t : TangentVector 𝒳 x) :
    (t.smul c).hom ≫ pullbackMap t.pt.2 (specDualNumberSmul k c) = t.hom :=
  IsStronglyCartesian.fac 𝒳.p (specDualNumberSmul k c)
    (pullbackMap t.pt.2 (specDualNumberSmul k c))
    (specDualNumberInclusion_comp_specDualNumberSmul k c).symm t.hom

/-- The scalar action on tangent vectors preserves the equivalence: representatives of
the same tangent space element have equivalent scalar multiples. -/
lemma Equiv.smul (c : k) {t t' : TangentVector 𝒳 x} (h : Equiv t t') :
    Equiv (t.smul c) (t'.smul c) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨⟨pullbackFunctorMap 𝒳.p (specDualNumberSmul k c) β,
    pullbackFunctorMap_isHomLift 𝒳.p (specDualNumberSmul k c) β⟩, ?_⟩
  change (t.smul c).hom ≫ pullbackFunctorMap 𝒳.p (specDualNumberSmul k c) β =
    (t'.smul c).hom
  have ht' := t'.isHomLift
  have hL : IsHomLift 𝒳.p (specDualNumberInclusion k)
      ((t.smul c).hom ≫ pullbackFunctorMap 𝒳.p (specDualNumberSmul k c) β) := by
    have h₁ := (t.smul c).isHomLift
    have h₂ := pullbackFunctorMap_isHomLift 𝒳.p (specDualNumberSmul k c) β
    have h₃ := IsHomLift.comp 𝒳.p (specDualNumberInclusion k)
      (𝟙 (Spec (CommRingCat.of (DualNumber k)))) (t.smul c).hom
      (pullbackFunctorMap 𝒳.p (specDualNumberSmul k c) β)
    simpa using h₃
  exact IsStronglyCartesian.map_uniq 𝒳.p (specDualNumberSmul k c)
    (pullbackMap t'.pt.2 (specDualNumberSmul k c))
    (specDualNumberInclusion_comp_specDualNumberSmul k c).symm t'.hom
    ((t.smul c).hom ≫ pullbackFunctorMap 𝒳.p (specDualNumberSmul k c) β)
    (by simp [hβ])

end TangentVector

/-- Supporting construction for Proposition 4.5.10: the scalar action of $k$ on the
tangent space $T_{\cX,x}$, where multiplication by
$c \in k$ pulls back an extension to the dual numbers along the rescaling
$\epsilon \mapsto c\epsilon$. (Together with the addition provided by the homogeneity
equivalence in the proposition, this makes $T_{\cX,x}$ a $k$-vector space; the
`Module` instance is deferred, see the ledger in the `PropTangentSpace` section.) -/
noncomputable def TangentSpace.smul [𝒳.p.IsFiberedInGroupoids] (c : k)
    {x : 𝒳.p.Fiber (Spec (CommRingCat.of k))} :
    TangentSpace 𝒳 x → TangentSpace 𝒳 x :=
  Quot.map (TangentVector.smul c) (fun _ _ h ↦ h.smul c)

end AlgebraicGeometry.BasedCategory

end DefTangentSpace

section ExMgTangentSpace

/- LEDGER (**Example 4.5.8**, `ex:mg-tangent-space`): for a smooth, connected,
projective curve `[C] ∈
𝓜_g(k)` of genus `g ≥ 2`, deformation theory identifies `T_{𝓜_g,[C]} = H¹(C, T_C)` and
Riemann–Roch computes `dim T_{𝓜_g,[C]} = 3g - 3`. Blocked on the moduli stack `𝓜_g`
(§3.4/§4.1 ledgers), first-order deformation theory
(`prop:first-order-deformations-of-a-smooth-scheme`, Appendix C), and coherent
cohomology with Riemann–Roch for curves (absent from Mathlib beyond divisor-level
Riemann–Roch). -/

end ExMgTangentSpace

section ExBunCTangentSpace

/- LEDGER (**Example 4.5.9**, `ex:bunC-tangent-space`): for a vector bundle
`E ∈ Bun_{r,d}(C)(k)` on a
smooth, connected, projective curve `C`, deformation theory identifies
`T_{Bun_{r,d}(C),[E]} = Ext¹(E, E) = H¹(C, E ⊗ E^∨)` and Riemann–Roch gives
`dim T = dim Aut(E) + r²(g-1)`. Blocked on the moduli stack `Bun_{r,d}(C)` (§3.4/§4.1
ledgers), deformations of coherent sheaves
(`prop:first-order-deformations-of-coherent-sheaves`, Appendix C), and Riemann–Roch for
coherent sheaves (`thm:riemann-roch-coherent-sheaves`). -/

end ExBunCTangentSpace

section PropTangentSpace

open CategoryTheory Functor CategoryTheory.Functor.IsPreFibered
  CategoryTheory.Functor.IsFibered CategoryTheory.BasedCategory AlgebraicGeometry
  TrivSqZeroExt

universe v₂ u₂ u

namespace AlgebraicGeometry.BasedCategory

/-- Background definition used in Proposition 4.5.10: a prestack $\cX$ over $\Sch$ has
*affine diagonal* if for
any two morphisms
$\Spec A \to \cX$ and $\Spec B \to \cX$ from affine schemes, the fiber product
$\Spec A \times_{\cX} \Spec B$ is (represented by) an affine scheme. (This is the
diagonal-free characterization of the affineness of $\Delta_{\cX} \colon \cX \to
\cX \times \cX$; the comparison with the diagonal morphism of §4.2 is deferred.) -/
def HasAffineDiagonal (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) : Prop :=
  ∀ (A B : CommRingCat.{u}) (f : overBased (Spec A) ⥤ᵇ 𝒳)
    (g : overBased (Spec B) ⥤ᵇ 𝒳),
    ∃ C : CommRingCat.{u}, (fiberProduct f g).IsRepresentedBy (Spec C)

end AlgebraicGeometry.BasedCategory

namespace AlgebraicGeometry

/-- The ring $k[\epsilon_1] \times_k k[\epsilon_2]$ — the fiber product of two copies of
the dual numbers over $k$ — realized concretely as the square-zero extension
$k \oplus (k \times k)$, i.e. `TrivSqZeroExt k (k × k)`. This is the first projection
$\Spec k[\epsilon_1] \to \Spec(k[\epsilon_1] \times_k k[\epsilon_2])$. -/
noncomputable def specDualNumberPairLeft (k : Type u) [Field k] :
    Spec (CommRingCat.of (DualNumber k)) ⟶
      Spec (CommRingCat.of (TrivSqZeroExt k (k × k))) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst k k k)).toRingHom)

/-- The second projection
$\Spec k[\epsilon_2] \to \Spec(k[\epsilon_1] \times_k k[\epsilon_2])$, with
$k[\epsilon_1] \times_k k[\epsilon_2]$ realized as `TrivSqZeroExt k (k × k)`. -/
noncomputable def specDualNumberPairRight (k : Type u) [Field k] :
    Spec (CommRingCat.of (DualNumber k)) ⟶
      Spec (CommRingCat.of (TrivSqZeroExt k (k × k))) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd k k k)).toRingHom)

/-- The closed point $\Spec k \to \Spec(k[\epsilon_1] \times_k k[\epsilon_2])$, with
$k[\epsilon_1] \times_k k[\epsilon_2]$ realized as `TrivSqZeroExt k (k × k)`. -/
noncomputable def specDualNumberPairBase (k : Type u) [Field k] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (TrivSqZeroExt k (k × k))) :=
  Spec.map (CommRingCat.ofHom (fstHom k k (k × k)).toRingHom)

/-- The closed point of $\Spec(k[\epsilon_1] \times_k k[\epsilon_2])$ factors through the
first copy of the dual numbers. -/
lemma specDualNumberInclusion_comp_specDualNumberPairLeft (k : Type u) [Field k] :
    specDualNumberInclusion k ≫ specDualNumberPairLeft k = specDualNumberPairBase k := by
  have h : (fstHom k k k).toRingHom.comp
      (TrivSqZeroExt.map (LinearMap.fst k k k)).toRingHom =
      (fstHom k k (k × k)).toRingHom :=
    congrArg AlgHom.toRingHom (fstHom_comp_map (LinearMap.fst k k k))
  rw [specDualNumberInclusion, specDualNumberPairLeft, specDualNumberPairBase,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- The closed point of $\Spec(k[\epsilon_1] \times_k k[\epsilon_2])$ factors through the
second copy of the dual numbers. -/
lemma specDualNumberInclusion_comp_specDualNumberPairRight (k : Type u) [Field k] :
    specDualNumberInclusion k ≫ specDualNumberPairRight k =
      specDualNumberPairBase k := by
  have h : (fstHom k k k).toRingHom.comp
      (TrivSqZeroExt.map (LinearMap.snd k k k)).toRingHom =
      (fstHom k k (k × k)).toRingHom :=
    congrArg AlgHom.toRingHom (fstHom_comp_map (LinearMap.snd k k k))
  rw [specDualNumberInclusion, specDualNumberPairRight, specDualNumberPairBase,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

end AlgebraicGeometry

namespace AlgebraicGeometry.BasedCategory

variable (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) (k : Type u) [Field k]

/-- Supporting definition for Proposition 4.5.10: an object of the 2-fiber product
$\cX(k[\epsilon_1]) \times_{\cX(k)}
\cX(k[\epsilon_2])$ in span form: objects $a_1$ over $\Spec k[\epsilon_1]$, $a_2$ over
$\Spec k[\epsilon_2]$, and $a_0$ over $\Spec k$, together with morphisms
$a_0 \to a_1$ and $a_0 \to a_2$ lying over the closed immersions
$\Spec k \to \Spec k[\epsilon_i]$. (Since $\cX$ is fibered in groupoids, these morphisms
are automatically cartesian, so the span form is equivalent to the pair-with-isomorphism
form of the 2-fiber product.) -/
structure DualNumberGluingDatum where
  /-- The object over `Spec k`. -/
  base : 𝒳.p.Fiber (Spec (CommRingCat.of k))
  /-- The object over the first copy of `Spec k[ε]`. -/
  left : 𝒳.p.Fiber (Spec (CommRingCat.of (DualNumber k)))
  /-- The object over the second copy of `Spec k[ε]`. -/
  right : 𝒳.p.Fiber (Spec (CommRingCat.of (DualNumber k)))
  /-- The restriction morphism to the first copy. -/
  leftHom : base.1 ⟶ left.1
  /-- The restriction morphism to the second copy. -/
  rightHom : base.1 ⟶ right.1
  /-- The first restriction morphism lies over `Spec k → Spec k[ε]`. -/
  isHomLift_leftHom : IsHomLift 𝒳.p (specDualNumberInclusion k) leftHom
  /-- The second restriction morphism lies over `Spec k → Spec k[ε]`. -/
  isHomLift_rightHom : IsHomLift 𝒳.p (specDualNumberInclusion k) rightHom

attribute [instance] DualNumberGluingDatum.isHomLift_leftHom
  DualNumberGluingDatum.isHomLift_rightHom

variable {𝒳 k}

/-- A morphism of gluing data over the dual numbers: a triple of morphisms in the three
fiber categories compatible with the restriction morphisms of the spans. -/
@[ext]
structure DualNumberGluingDatumHom (d d' : DualNumberGluingDatum 𝒳 k) where
  /-- The component over `Spec k`. -/
  baseHom : d.base ⟶ d'.base
  /-- The component over the first copy of `Spec k[ε]`. -/
  leftHom : d.left ⟶ d'.left
  /-- The component over the second copy of `Spec k[ε]`. -/
  rightHom : d.right ⟶ d'.right
  /-- Compatibility with the first restriction morphisms. -/
  wLeft : d.leftHom ≫ Fiber.fiberInclusion.map leftHom =
    Fiber.fiberInclusion.map baseHom ≫ d'.leftHom
  /-- Compatibility with the second restriction morphisms. -/
  wRight : d.rightHom ≫ Fiber.fiberInclusion.map rightHom =
    Fiber.fiberInclusion.map baseHom ≫ d'.rightHom

attribute [reassoc] DualNumberGluingDatumHom.wLeft DualNumberGluingDatumHom.wRight

/-- The identity morphism of a gluing datum over the dual numbers. -/
@[simps]
noncomputable def DualNumberGluingDatumHom.id (d : DualNumberGluingDatum 𝒳 k) :
    DualNumberGluingDatumHom d d where
  baseHom := 𝟙 d.base
  leftHom := 𝟙 d.left
  rightHom := 𝟙 d.right
  wLeft := by
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    exact Category.comp_id d.leftHom
  wRight := by
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    exact Category.comp_id d.rightHom

/-- The composition of morphisms of gluing data over the dual numbers. -/
@[simps]
noncomputable def DualNumberGluingDatumHom.comp {d d' d'' : DualNumberGluingDatum 𝒳 k}
    (φ : DualNumberGluingDatumHom d d') (ψ : DualNumberGluingDatumHom d' d'') :
    DualNumberGluingDatumHom d d'' where
  baseHom := φ.baseHom ≫ ψ.baseHom
  leftHom := φ.leftHom ≫ ψ.leftHom
  rightHom := φ.rightHom ≫ ψ.rightHom
  wLeft := by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, φ.wLeft, Category.assoc,
      ψ.wLeft, ← Category.assoc]
  wRight := by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, φ.wRight, Category.assoc,
      ψ.wRight, ← Category.assoc]

noncomputable instance DualNumberGluingDatum.instCategory :
    Category (DualNumberGluingDatum 𝒳 k) where
  Hom d d' := DualNumberGluingDatumHom d d'
  id d := DualNumberGluingDatumHom.id d
  comp φ ψ := φ.comp ψ
  id_comp φ := by ext <;> simp
  comp_id φ := by ext <;> simp
  assoc φ ψ χ := by ext <;> simp

/-- The base component of an identity morphism of gluing data. -/
@[simp]
lemma DualNumberGluingDatum.id_baseHom (d : DualNumberGluingDatum 𝒳 k) :
    DualNumberGluingDatumHom.baseHom (𝟙 d) = 𝟙 d.base :=
  rfl

/-- The left component of an identity morphism of gluing data. -/
@[simp]
lemma DualNumberGluingDatum.id_leftHom (d : DualNumberGluingDatum 𝒳 k) :
    DualNumberGluingDatumHom.leftHom (𝟙 d) = 𝟙 d.left :=
  rfl

/-- The right component of an identity morphism of gluing data. -/
@[simp]
lemma DualNumberGluingDatum.id_rightHom (d : DualNumberGluingDatum 𝒳 k) :
    DualNumberGluingDatumHom.rightHom (𝟙 d) = 𝟙 d.right :=
  rfl

/-- The base component of a composition of morphisms of gluing data. -/
@[simp]
lemma DualNumberGluingDatum.comp_baseHom {d d' d'' : DualNumberGluingDatum 𝒳 k}
    (φ : d ⟶ d') (ψ : d' ⟶ d'') :
    DualNumberGluingDatumHom.baseHom (φ ≫ ψ) = φ.baseHom ≫ ψ.baseHom :=
  rfl

/-- The left component of a composition of morphisms of gluing data. -/
@[simp]
lemma DualNumberGluingDatum.comp_leftHom {d d' d'' : DualNumberGluingDatum 𝒳 k}
    (φ : d ⟶ d') (ψ : d' ⟶ d'') :
    DualNumberGluingDatumHom.leftHom (φ ≫ ψ) = φ.leftHom ≫ ψ.leftHom :=
  rfl

/-- The right component of a composition of morphisms of gluing data. -/
@[simp]
lemma DualNumberGluingDatum.comp_rightHom {d d' d'' : DualNumberGluingDatum 𝒳 k}
    (φ : d ⟶ d') (ψ : d' ⟶ d'') :
    DualNumberGluingDatumHom.rightHom (φ ≫ ψ) = φ.rightHom ≫ ψ.rightHom :=
  rfl

variable (𝒳 k) in
/-- Supporting comparison functor for the proof of Proposition 4.5.10:
$\cX(k[\epsilon_1] \times_k k[\epsilon_2]) \to \cX(k[\epsilon_1]) \times_{\cX(k)}
\cX(k[\epsilon_2])$: an object over
$\Spec(k[\epsilon_1] \times_k k[\epsilon_2])$ restricts (by chosen cartesian pullbacks)
to objects over $\Spec k[\epsilon_1]$, $\Spec k[\epsilon_2]$, and $\Spec k$, connected by
the transition morphisms over the closed immersions. -/
noncomputable def dualNumberGluingComparison [𝒳.p.IsFiberedInGroupoids] :
    𝒳.p.Fiber (Spec (CommRingCat.of (TrivSqZeroExt k (k × k)))) ⥤
      DualNumberGluingDatum 𝒳 k where
  obj b :=
    { base := Fiber.mk (pullbackObj_proj b.2 (specDualNumberPairBase k))
      left := Fiber.mk (pullbackObj_proj b.2 (specDualNumberPairLeft k))
      right := Fiber.mk (pullbackObj_proj b.2 (specDualNumberPairRight k))
      leftHom := pullbackTransition 𝒳.p (specDualNumberPairLeft k)
        (specDualNumberInclusion_comp_specDualNumberPairLeft k).symm b
      rightHom := pullbackTransition 𝒳.p (specDualNumberPairRight k)
        (specDualNumberInclusion_comp_specDualNumberPairRight k).symm b
      isHomLift_leftHom := pullbackTransition_isHomLift 𝒳.p (specDualNumberPairLeft k)
        (specDualNumberInclusion_comp_specDualNumberPairLeft k).symm b
      isHomLift_rightHom := pullbackTransition_isHomLift 𝒳.p
        (specDualNumberPairRight k)
        (specDualNumberInclusion_comp_specDualNumberPairRight k).symm b }
  map {b b'} ψ :=
    { baseHom := ⟨pullbackFunctorMap 𝒳.p (specDualNumberPairBase k) ψ,
        pullbackFunctorMap_isHomLift 𝒳.p (specDualNumberPairBase k) ψ⟩
      leftHom := ⟨pullbackFunctorMap 𝒳.p (specDualNumberPairLeft k) ψ,
        pullbackFunctorMap_isHomLift 𝒳.p (specDualNumberPairLeft k) ψ⟩
      rightHom := ⟨pullbackFunctorMap 𝒳.p (specDualNumberPairRight k) ψ,
        pullbackFunctorMap_isHomLift 𝒳.p (specDualNumberPairRight k) ψ⟩
      wLeft := pullbackTransition_naturality 𝒳.p (specDualNumberPairLeft k)
        (specDualNumberInclusion_comp_specDualNumberPairLeft k).symm ψ
      wRight := pullbackTransition_naturality 𝒳.p (specDualNumberPairRight k)
        (specDualNumberInclusion_comp_specDualNumberPairRight k).symm ψ }
  map_id b := by
    refine DualNumberGluingDatumHom.ext ?_ ?_ ?_ <;>
      · apply Fiber.hom_ext
        change pullbackFunctorMap 𝒳.p _ (𝟙 b) = 𝟙 _
        simp
  map_comp {b b' b''} ψ χ := by
    refine DualNumberGluingDatumHom.ext ?_ ?_ ?_ <;>
      · apply Fiber.hom_ext
        change pullbackFunctorMap 𝒳.p _ (ψ ≫ χ) =
          pullbackFunctorMap 𝒳.p _ ψ ≫ pullbackFunctorMap 𝒳.p _ χ
        simp

/-- Supporting homogeneity equivalence for the proof of Proposition 4.5.10 (the display's
stray label is discussed in COMMENTARY.md): let $\cX$ be an algebraic
stack with affine diagonal and $k$ a field. Then the comparison functor
$\cX(k[\epsilon_1] \times_k k[\epsilon_2]) \to \cX(k[\epsilon_1]) \times_{\cX(k)}
\cX(k[\epsilon_2])$ is an equivalence of categories; equivalently, the square of closed
immersions of $\Spec k$, $\Spec k[\epsilon_i]$, and
$\Spec(k[\epsilon_1] \times_k k[\epsilon_2])$ is a pushout among algebraic stacks with
affine diagonal. This provides the addition on the tangent spaces of $\cX$. -/
theorem isEquivalence_dualNumberGluingComparison
    (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) (k : Type u) [Field k]
    [AlgebraicGeometry.IsAlgebraicStack 𝒳] (h : HasAffineDiagonal 𝒳) :
    (dualNumberGluingComparison 𝒳 k).IsEquivalence := by
  sorry

/- LEDGER (**Proposition 4.5.10**, `prop:tangent-space`, the
`Module k (TangentSpace 𝒳 x)` instance): the
addition on `T_{𝒳,x}` is defined through the homogeneity equivalence
`isEquivalence_dualNumberGluingComparison` (composing a quasi-inverse with the morphism
`Spec k[ε] → Spec (k[ε₁] ×ₖ k[ε₂])` sending both `εᵢ` to `ε`), and the vector space
axioms require the compatibilities of that equivalence. Both are blocked on the proof of
the homogeneity equivalence, which needs the Flatness Criterion over Artinian Rings
(`prop:flatness-criterion-over-artinian-rings`, Appendix A) and descent along smooth
presentations (cf. Stacks 07WN region); the `Module` instance is therefore deferred with
it. -/

/- LEDGER (the unlabeled hard exercise after **Proposition 4.5.10**,
`prop:tangent-space`): (a) the tangent space
`T_{𝒳,x}` is naturally a representation of the stabilizer group `G_x`, acting by
`g ⋅ (τ, α) = (τ, g ∘ α)` — blocked on stabilizer group schemes, which require the
Isom presheaf (`exer:isom-presheaf`, §3.4 ledger) and the §4.2 inertia and stabilizer
constructions. (b) the affine-diagonal hypothesis in `prop:tangent-space` is
superfluous — blocked on the proof of the homogeneity equivalence above. -/

end AlgebraicGeometry.BasedCategory

end PropTangentSpace
