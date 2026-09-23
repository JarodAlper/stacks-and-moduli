module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Quotient.Basic
public import StacksAndModuli.API.PolynomialHyperplane
public import StacksAndModuli.API.HomogeneousDimension

/-!
# Graded modules over the standard graded polynomial ring

Supporting API with no Stacks Project counterpart, developed for §2.3 (Castelnuovo–Mumford
regularity) of *Stacks and Moduli*.

Mathlib has no quasi-coherent sheaves on `Proj` — neither the twisting sheaves `𝒪(d)` nor the
functor `M ↦ M~` — so the sheaf-level statements of §2.3 cannot be written directly. This file
supplies the standard algebraic model: a quasi-coherent sheaf on `ℙⁿ_k` is presented by a
`ℤ`-graded module over `S = k[x₀, …, x_n]`, and the sheaf-theoretic operations used in §2.3
(twist, restriction to a coordinate hyperplane, direct sums, short exact sequences) are the
corresponding module operations. See `StacksAndModuli/Section2.3-Regularity/COMMENTARY.md`.

A `ℤ`-graded `S`-module is encoded *by its graded pieces*: a family `M d` of `k`-modules
(`d : ℤ`) together with `n+1` pairwise commuting degree-raising maps, multiplication by the
variables `x₀, …, x_n`. This encoding avoids `DirectSum.Decomposition` bookkeeping entirely and
makes the twist `M(a)` a reindexing.

Main declarations:
- `AlgebraicGeometry.ProjectiveSpace.GradedModule`: the graded-piece encoding, with its
  category structure (`Hom`, `Category`).
- `AlgebraicGeometry.ProjectiveSpace.GradedModule.twist`: the Serre twist `M(a)`.
- `AlgebraicGeometry.ProjectiveSpace.GradedModule.polySubmodule`,
  `AlgebraicGeometry.ProjectiveSpace.GradedModule.structureModule`: the graded ring `S` itself,
  i.e. the structure sheaf; `GradedModule.twistingModule a` is `𝒪(a)`.
- `AlgebraicGeometry.ProjectiveSpace.GradedModule.pi`: finite direct sums, so `𝒪(a)^{⊕r}`.
- `AlgebraicGeometry.ProjectiveSpace.GradedModule.ShortExact`: degreewise short exactness.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open CategoryTheory

variable (k : Type u) [CommRing k] (n : ℕ)

/-- A `ℤ`-graded module over the standard graded polynomial ring `k[x₀, …, x_n]`, encoded by
its graded pieces: a family of `k`-modules `obj d` indexed by `d : ℤ`, together with `n+1`
pairwise commuting degree-raising maps `mulX i`, "multiplication by the variable `xᵢ`".

This is the algebraic model of a quasi-coherent sheaf on `ℙⁿ_k` used throughout §2.3. -/
structure GradedModule where
  /-- The degree-`d` graded piece. -/
  obj : ℤ → ModuleCat.{u} k
  /-- Multiplication by the variable `xᵢ`, a map of degree `+1`. -/
  mulX : ∀ (_i : Fin (n + 1)) (d : ℤ), obj d ⟶ obj (d + 1)
  /-- The variables commute. -/
  mulX_comm : ∀ (i j : Fin (n + 1)) (d : ℤ),
    mulX i d ≫ mulX j (d + 1) = mulX j d ≫ mulX i (d + 1)

namespace GradedModule

variable {k n}

/-- A morphism of graded modules: a degreewise `k`-linear map commuting with the variables. -/
@[ext]
structure Hom (M N : GradedModule k n) where
  /-- The degree-`d` component. -/
  app : ∀ d : ℤ, M.obj d ⟶ N.obj d
  /-- Compatibility with multiplication by the variables. -/
  comm : ∀ (i : Fin (n + 1)) (d : ℤ), app d ≫ N.mulX i d = M.mulX i d ≫ app (d + 1) := by
    aesop_cat

attribute [reassoc] Hom.comm

instance : Category (GradedModule k n) where
  Hom M N := Hom M N
  id _ := { app := fun _ => 𝟙 _ }
  comp f g :=
    { app := fun d => f.app d ≫ g.app d
      comm := fun i d => by
        rw [Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc] }

@[simp] lemma id_app (M : GradedModule k n) (d : ℤ) : Hom.app (𝟙 M) d = 𝟙 _ := rfl

@[simp] lemma comp_app {M N P : GradedModule k n} (f : M ⟶ N) (g : N ⟶ P) (d : ℤ) :
    (f ≫ g).app d = f.app d ≫ g.app d := rfl

@[ext] lemma hom_ext {M N : GradedModule k n} {f g : M ⟶ N} (h : ∀ d, f.app d = g.app d) :
    f = g :=
  Hom.ext (funext h)

/-- Multiplication by `xᵢ` from degree `d` to a degree `e` presented together with a proof of
`d + 1 = e`. Using this in place of `mulX` keeps degree arithmetic out of statements. -/
def mulX' (M : GradedModule k n) (i : Fin (n + 1)) (d e : ℤ) (h : d + 1 = e) :
    M.obj d ⟶ M.obj e :=
  M.mulX i d ≫ eqToHom (congrArg M.obj h)

@[simp] lemma mulX'_rfl (M : GradedModule k n) (i : Fin (n + 1)) (d : ℤ) :
    M.mulX' i d (d + 1) rfl = M.mulX i d := by
  simp [mulX']

lemma mulX'_comm (M : GradedModule k n) (i j : Fin (n + 1)) (d e e' f : ℤ)
    (h₁ : d + 1 = e) (h₂ : e + 1 = f) (h₁' : d + 1 = e') (h₂' : e' + 1 = f) :
    M.mulX' i d e h₁ ≫ M.mulX' j e f h₂ = M.mulX' j d e' h₁' ≫ M.mulX' i e' f h₂' := by
  have he : e = e' := by omega
  subst he; subst h₁; subst h₂
  simpa using M.mulX_comm i j d

lemma Hom.comm' {M N : GradedModule k n} (f : M ⟶ N) (i : Fin (n + 1)) (d e : ℤ)
    (h : d + 1 = e) : f.app d ≫ N.mulX' i d e h = M.mulX' i d e h ≫ f.app e := by
  subst h; simpa using f.comm i d

/-- A short exact sequence `0 → M → N → P → 0` of graded modules: degreewise short exact. -/
structure ShortExact {M N P : GradedModule k n} (f : M ⟶ N) (g : N ⟶ P) : Prop where
  /-- The first map is degreewise injective. -/
  injective : ∀ d, Function.Injective (f.app d).hom
  /-- Exactness in the middle, degreewise. -/
  exact : ∀ d, LinearMap.range (f.app d).hom = LinearMap.ker (g.app d).hom
  /-- The second map is degreewise surjective. -/
  surjective : ∀ d, Function.Surjective (g.app d).hom

/-- The Serre twist `M(a)`: the graded module whose degree-`d` piece is `M_{d+a}`. -/
def twist (M : GradedModule k n) (a : ℤ) : GradedModule k n where
  obj d := M.obj (d + a)
  mulX i d := M.mulX' i (d + a) (d + 1 + a) (by ring)
  mulX_comm i j d :=
    M.mulX'_comm i j (d + a) (d + 1 + a) (d + 1 + a) (d + 1 + 1 + a) (by ring) (by ring)
      (by ring) (by ring)

@[simp] lemma twist_obj (M : GradedModule k n) (a d : ℤ) : (M.twist a).obj d = M.obj (d + a) := rfl

@[simp] lemma twist_mulX (M : GradedModule k n) (a : ℤ) (i : Fin (n + 1)) (d : ℤ) :
    (M.twist a).mulX i d = M.mulX' i (d + a) (d + 1 + a) (by ring) := rfl

/-- A morphism of graded modules twists. -/
def twistMap {M N : GradedModule k n} (f : M ⟶ N) (a : ℤ) : M.twist a ⟶ N.twist a where
  app d := f.app (d + a)
  comm i d := f.comm' i (d + a) (d + 1 + a) (by ring)

@[simp] lemma twistMap_app {M N : GradedModule k n} (f : M ⟶ N) (a d : ℤ) :
    (twistMap f a).app d = f.app (d + a) := rfl

/-- The Serre twist as a functor. -/
def twistFunctor (a : ℤ) : GradedModule k n ⥤ GradedModule k n where
  obj M := M.twist a
  map f := twistMap f a

variable (k n)

/-- The degree-`e` graded piece of `S = k[x₀, …, x_n]`, declared to be zero in negative
degrees. -/
noncomputable def polySubmodule (e : ℤ) : Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  if 0 ≤ e then MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k e.toNat else ⊥

lemma polySubmodule_of_nonneg {e : ℤ} (he : 0 ≤ e) :
    polySubmodule k n e = MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k e.toNat := by
  simp only [polySubmodule, he, ↓reduceIte]

lemma polySubmodule_of_neg {e : ℤ} (he : e < 0) : polySubmodule k n e = ⊥ := by
  simp only [polySubmodule, Int.not_le.mpr he, ↓reduceIte]

lemma X_mul_mem_polySubmodule (i : Fin (n + 1)) (e : ℤ) {p : MvPolynomial (Fin (n + 1)) k}
    (hp : p ∈ polySubmodule k n e) : MvPolynomial.X i * p ∈ polySubmodule k n (e + 1) := by
  rcases lt_or_ge e 0 with he | he
  · rw [polySubmodule_of_neg k n he, Submodule.mem_bot] at hp
    subst hp
    simp
  · rw [polySubmodule_of_nonneg k n he] at hp
    rw [polySubmodule_of_nonneg k n (by omega), MvPolynomial.mem_homogeneousSubmodule]
    have h : (e + 1).toNat = 1 + e.toNat := by omega
    rw [h]
    exact (MvPolynomial.isHomogeneous_X (R := k) i).mul hp

/-- Multiplication by `xᵢ` on the graded pieces of `S = k[x₀, …, x_n]`. -/
noncomputable def polyMulX (i : Fin (n + 1)) (e : ℤ) :
    polySubmodule k n e →ₗ[k] polySubmodule k n (e + 1) where
  toFun p := ⟨MvPolynomial.X i * p.1, X_mul_mem_polySubmodule k n i e p.2⟩
  map_add' p q := Subtype.ext (by simp [mul_add])
  map_smul' c p := Subtype.ext (by simp)

/-- The structure sheaf of `ℙⁿ_k`: the graded ring `S = k[x₀, …, x_n]` viewed as a graded
module over itself. -/
noncomputable def structureModule : GradedModule k n where
  obj d := ModuleCat.of k (polySubmodule k n d)
  mulX i d := ModuleCat.ofHom (polyMulX k n i d)
  mulX_comm i j d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun p => Subtype.ext ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, polyMulX,
      LinearMap.coe_mk, AddHom.coe_mk]
    ring

/-- The twisting sheaf `𝒪(a)` on `ℙⁿ_k`, i.e. the graded module `S(a)`. -/
noncomputable def twistingModule (a : ℤ) : GradedModule k n := (structureModule k n).twist a

variable {k n}

/-- The direct sum `M^{⊕r}` of `r` copies of `M`. -/
def pow (M : GradedModule k n) (r : ℕ) : GradedModule k n where
  obj d := ModuleCat.of k (Fin r → M.obj d)
  mulX i d := ModuleCat.ofHom (LinearMap.pi fun j => (M.mulX i d).hom.comp (LinearMap.proj j))
  mulX_comm i j d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun m => funext fun l => ?_)
    simpa using congrArg (fun f : M.obj d ⟶ M.obj (d + 1 + 1) => f.hom (m l))
      (M.mulX_comm i j d)

/-- Multiplication by the linear form `L = ∑ cᵢ xᵢ`, from degree `d` to a degree `e`
presented together with a proof of `d + 1 = e`. -/
noncomputable def mulL (M : GradedModule k n) (c : Fin (n + 1) → k) (d e : ℤ) (h : d + 1 = e) :
    M.obj d ⟶ M.obj e :=
  ∑ i, c i • M.mulX' i d e h

lemma mulX'_comp_mulL (M : GradedModule k n) (c : Fin (n + 1) → k) (i : Fin (n + 1))
    (d e e' f : ℤ) (h₁ : d + 1 = e) (h₂ : e + 1 = f) (h₁' : d + 1 = e') (h₂' : e' + 1 = f) :
    M.mulX' i d e h₁ ≫ M.mulL c e f h₂ = M.mulL c d e' h₁' ≫ M.mulX' i e' f h₂' := by
  have he : e = e' := by omega
  subst he
  simp only [mulL, Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_smul, Linear.smul_comp]
  exact Finset.sum_congr rfl fun j _ =>
    congrArg (c j • ·) (M.mulX'_comm i j d e e f h₁ h₂ h₁' h₂')

lemma comm_mulL {M N : GradedModule k n} (f : M ⟶ N) (c : Fin (n + 1) → k) (d e : ℤ)
    (h : d + 1 = e) : f.app d ≫ N.mulL c d e h = M.mulL c d e h ≫ f.app e := by
  simp only [mulL, Preadditive.comp_sum, Preadditive.sum_comp, Linear.smul_comp, Linear.comp_smul]
  exact Finset.sum_congr rfl fun j _ => congrArg (c j • ·) (f.comm' j d e h)

/-- The degreewise cokernel of a morphism of graded modules. -/
noncomputable def coker {A B : GradedModule k n} (f : A ⟶ B) : GradedModule k n where
  obj d := ModuleCat.of k ((B.obj d) ⧸ LinearMap.range (f.app d).hom)
  mulX i d := ModuleCat.ofHom (Submodule.mapQ _ _ (B.mulX i d).hom (by
    rintro x ⟨y, rfl⟩
    exact ⟨(A.mulX i d).hom y,
      congrArg (fun g : A.obj d ⟶ B.obj (d + 1) => g.hom y) (f.comm i d).symm⟩))
  mulX_comm i j d := by
    refine ModuleCat.hom_ext (LinearMap.ext ?_)
    rintro ⟨x⟩
    exact congrArg (Submodule.Quotient.mk (p := LinearMap.range (f.app (d + 1 + 1)).hom))
      (congrArg (fun g : B.obj d ⟶ B.obj (d + 1 + 1) => g.hom x) (B.mulX_comm i j d))

@[simp] lemma coker_obj {A B : GradedModule k n} (f : A ⟶ B) (d : ℤ) :
    (coker f).obj d = ModuleCat.of k ((B.obj d) ⧸ LinearMap.range (f.app d).hom) := rfl

/-- The projection onto the degreewise cokernel. -/
noncomputable def toCoker {A B : GradedModule k n} (f : A ⟶ B) : B ⟶ coker f where
  app d := ModuleCat.ofHom (LinearMap.range (f.app d).hom).mkQ
  comm _ _ := rfl

/-- Multiplication by the linear form `L = ∑ cᵢ xᵢ`, as a morphism `M(-1) → M`. -/
noncomputable def mulLHom (M : GradedModule k n) (c : Fin (n + 1) → k) : M.twist (-1) ⟶ M where
  app d := M.mulL c (d + -1) d (by ring)
  comm i d :=
    (M.mulX'_comp_mulL c i (d + -1) (d + 1 + -1) d (d + 1) (by ring) (by ring)
      (by ring) (by ring)).symm

@[simp] lemma mulLHom_app (M : GradedModule k n) (c : Fin (n + 1) → k) (d : ℤ) :
    (M.mulLHom c).app d = M.mulL c (d + -1) d (by ring) := rfl

/-- The restriction `M/LM` of `M` to the hyperplane `H = V(L)`, still regarded as a graded
module over `k[x₀, …, x_n]`. It models the pushforward of `F|_H` along the closed immersion
`H ↪ ℙⁿ`. -/
noncomputable def quotL (M : GradedModule k n) (c : Fin (n + 1) → k) : GradedModule k n :=
  coker (M.mulLHom c)

/-- Forget the action of the variable `x_j`. A graded module over `k[x₀, …, x_{n+1}]` killed by a
linear form whose `x_j`-coefficient is a unit is a graded module over the remaining variables,
i.e. a quasi-coherent sheaf on the hyperplane `H ≅ ℙⁿ`. -/
def dropVar (N : GradedModule k (n + 1)) (j : Fin (n + 2)) : GradedModule k n where
  obj := N.obj
  mulX i d := N.mulX (j.succAbove i) d
  mulX_comm _ _ d := N.mulX_comm _ _ d

@[simp] lemma dropVar_obj (N : GradedModule k (n + 1)) (j : Fin (n + 2)) (d : ℤ) :
    (N.dropVar j).obj d = N.obj d := rfl

/-- The restriction `F|_H` of `M` to the hyperplane `H = V(L)`, as a graded module over the
polynomial ring in the remaining `n+1` variables, i.e. a quasi-coherent sheaf on `H ≅ ℙⁿ`. -/
noncomputable def restrictL (M : GradedModule k (n + 1)) (c : Fin (n + 2) → k)
    (j : Fin (n + 2)) : GradedModule k n :=
  (M.quotL c).dropVar j

/-- The degreewise kernel of a morphism of graded modules. -/
noncomputable def ker {A B : GradedModule k n} (f : A ⟶ B) : GradedModule k n where
  obj d := ModuleCat.of k (LinearMap.ker (f.app d).hom)
  mulX i d := ModuleCat.ofHom ((A.mulX i d).hom.restrict (p := LinearMap.ker (f.app d).hom)
    (q := LinearMap.ker (f.app (d + 1)).hom) (fun x hx => by
      have h := congrArg (fun g : A.obj d ⟶ B.obj (d + 1) => g.hom x) (f.comm i d)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← h, hx, map_zero]))
  mulX_comm i j d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact congrArg (fun g : A.obj d ⟶ A.obj (d + 1 + 1) => g.hom x.1) (A.mulX_comm i j d)

/-- The inclusion of the degreewise kernel. -/
noncomputable def kerι {A B : GradedModule k n} (f : A ⟶ B) : ker f ⟶ A where
  app d := ModuleCat.ofHom (LinearMap.ker (f.app d).hom).subtype
  comm _ _ := rfl

/-- The inclusion of the kernel of a degreewise surjective morphism gives a short exact
sequence. -/
lemma shortExact_kerι {A B : GradedModule k n} (g : A ⟶ B)
    (hg : ∀ d, Function.Surjective (g.app d).hom) : ShortExact (kerι g) g where
  injective _ := Subtype.val_injective
  exact _ := Submodule.range_subtype _
  surjective := hg

/-- The universal property of the degreewise kernel: a morphism killed by `g` factors
through `ker g`. -/
noncomputable def kerLift {A B X : GradedModule k n} (g : A ⟶ B) (h : X ⟶ A)
    (hh : ∀ (d : ℤ) (x : X.obj d), (g.app d).hom ((h.app d).hom x) = 0) : X ⟶ ker g where
  app d := ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker (g.app d).hom)
    (h.app d).hom (fun x => LinearMap.mem_ker.mpr (hh d x)))
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact congrArg (fun t : X.obj d ⟶ A.obj (d + 1) => t.hom x) (h.comm i d)

@[simp] lemma kerLift_app_val {A B X : GradedModule k n} (g : A ⟶ B) (h : X ⟶ A)
    (hh : ∀ (d : ℤ) (x : X.obj d), (g.app d).hom ((h.app d).hom x) = 0) (d : ℤ)
    (x : X.obj d) : (((kerLift g h hh).app d).hom x).1 = (h.app d).hom x := rfl

lemma kerLift_kerι {A B X : GradedModule k n} (g : A ⟶ B) (h : X ⟶ A)
    (hh : ∀ (d : ℤ) (x : X.obj d), (g.app d).hom ((h.app d).hom x) = 0) :
    kerLift g h hh ≫ kerι g = h := rfl

lemma injective_kerLift {A B X : GradedModule k n} (g : A ⟶ B) (h : X ⟶ A)
    (hh : ∀ (d : ℤ) (x : X.obj d), (g.app d).hom ((h.app d).hom x) = 0)
    (hinj : ∀ d, Function.Injective (h.app d).hom) (d : ℤ) :
    Function.Injective (((kerLift g h hh).app d).hom) := fun x y hxy =>
  hinj d (congrArg Subtype.val hxy)

/-- The projection to the cokernel of a degreewise injective morphism gives a short exact
sequence. -/
lemma shortExact_toCoker {A B : GradedModule k n} (f : A ⟶ B)
    (hf : ∀ d, Function.Injective (f.app d).hom) : ShortExact f (toCoker f) where
  injective := hf
  exact _ := (Submodule.ker_mkQ _).symm
  surjective _ := Submodule.mkQ_surjective _

/-- Multiplication by the monomial `∏_{i ∈ l} xᵢ` indexed by a list of variables, from degree
`d` to a degree `e` presented together with a proof of `d + l.length = e`. -/
noncomputable def mulList (M : GradedModule k n) :
    ∀ (l : List (Fin (n + 1))) (d e : ℤ), d + (l.length : ℤ) = e → (M.obj d ⟶ M.obj e)
  | [], _, _, h => eqToHom (congrArg M.obj (by simpa using h))
  | i :: t, d, e, h =>
      M.mulX i d ≫ M.mulList t (d + 1) e (by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
        omega)

/-- The `k`-submodule of `M_e` spanned by all products `m · s` with `m` a monomial of degree
`e - d` and `s ∈ M_d`; equivalently the image of the multiplication map
`S_{e-d} ⊗ M_d → M_e`. -/
noncomputable def mulSpan (M : GradedModule k n) (d e : ℤ) : Submodule k (M.obj e) :=
  ⨆ l : {l : List (Fin (n + 1)) // d + (l.length : ℤ) = e},
    LinearMap.range (M.mulList l.1 d e l.2).hom

lemma le_mulSpan (M : GradedModule k n) (d e : ℤ) (l : List (Fin (n + 1)))
    (h : d + (l.length : ℤ) = e) :
    LinearMap.range (M.mulList l d e h).hom ≤ M.mulSpan d e :=
  le_iSup (fun l : {l : List (Fin (n + 1)) // d + (l.length : ℤ) = e} =>
    LinearMap.range (M.mulList l.1 d e l.2).hom) ⟨l, h⟩

lemma range_mulL_eq (M : GradedModule k n) (c : Fin (n + 1) → k) (d d' e : ℤ)
    (h : d + 1 = e) (h' : d' + 1 = e) :
    LinearMap.range (M.mulL c d e h).hom = LinearMap.range (M.mulL c d' e h').hom := by
  have hdd : d = d' := by omega
  subst hdd
  rfl

lemma range_mulX'_eq (M : GradedModule k n) (i : Fin (n + 1)) (d d' e : ℤ)
    (h : d + 1 = e) (h' : d' + 1 = e) :
    LinearMap.range (M.mulX' i d e h).hom = LinearMap.range (M.mulX' i d' e h').hom := by
  have hdd : d = d' := by omega
  subst hdd
  rfl

@[simp] lemma toCoker_app {A B : GradedModule k n} (f : A ⟶ B) (d : ℤ) :
    (toCoker f).app d = ModuleCat.ofHom (LinearMap.range (f.app d).hom).mkQ := rfl

lemma surjective_toCoker_app {A B : GradedModule k n} (f : A ⟶ B) (d : ℤ) :
    Function.Surjective ((toCoker f).app d).hom :=
  Submodule.mkQ_surjective _

/-- A cokernel of `M(-1) → M` given by multiplication by a linear form is killed by that
linear form: `M/LM` is a module over `S/(L)`, i.e. a sheaf on the hyperplane `V(L)`. -/
lemma quotL_mulL_eq_zero (M : GradedModule k n) (c : Fin (n + 1) → k) (d e : ℤ)
    (h : d + 1 = e) : (M.quotL c).mulL c d e h = 0 := by
  suffices hs : (coker (M.mulLHom c)).mulL c d e h = 0 from hs
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := surjective_toCoker_app (M.mulLHom c) d x
  have hcomm := congrArg (fun g : M.obj d ⟶ (coker (M.mulLHom c)).obj e => g.hom y)
    (comm_mulL (toCoker (M.mulLHom c)) c d e h)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  have hmem : (M.mulL c d e h).hom y ∈ LinearMap.range ((M.mulLHom c).app e).hom := by
    rw [mulLHom_app, range_mulL_eq M c (e + -1) d e (by ring) h]
    exact LinearMap.mem_range_self _ _
  have hzero : ((toCoker (M.mulLHom c)).app e).hom ((M.mulL c d e h).hom y) = 0 := by
    simp only [toCoker_app, ModuleCat.hom_ofHom]
    exact LinearMap.mem_ker.mp (by rw [Submodule.ker_mkQ]; exact hmem)
  rw [ModuleCat.hom_zero, LinearMap.zero_apply]
  exact hcomm.trans hzero

lemma mulList_append (M : GradedModule k n) (l₁ l₂ : List (Fin (n + 1))) (d e f : ℤ)
    (h₁ : d + (l₁.length : ℤ) = e) (h₂ : e + (l₂.length : ℤ) = f)
    (h : d + ((l₁ ++ l₂).length : ℤ) = f) :
    M.mulList (l₁ ++ l₂) d f h = M.mulList l₁ d e h₁ ≫ M.mulList l₂ e f h₂ := by
  induction l₁ generalizing d e with
  | nil =>
      have hde : d = e := by simpa using h₁
      subst hde
      simp only [List.nil_append, mulList]
      simp
  | cons i t ih =>
      have h₁' : d + 1 + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h₁; omega
      simp only [List.cons_append, mulList, Category.assoc]
      rw [ih (d + 1) e h₁' (by
        simp only [List.length_append, Nat.cast_add] at h ⊢
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
        omega)]

lemma mulSpan_trans (M : GradedModule k n) {d e f : ℤ}
    (hde : M.mulSpan d e = ⊤) (hef : M.mulSpan e f = ⊤) : M.mulSpan d f = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x ∈ M.mulSpan e f := hef ▸ Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun z => z ∈ M.mulSpan d f) hx ?_ ?_ ?_
  · rintro ⟨l₂, hl₂⟩ z ⟨y, rfl⟩
    have hy : y ∈ M.mulSpan d e := hde ▸ Submodule.mem_top
    refine Submodule.iSup_induction _
      (motive := fun w => (M.mulList l₂ e f hl₂).hom w ∈ M.mulSpan d f) hy ?_ ?_ ?_
    · rintro ⟨l₁, hl₁⟩ w ⟨v, rfl⟩
      refine le_mulSpan M d f (l₁ ++ l₂) (by
        simp only [List.length_append, Nat.cast_add]; omega) ?_
      refine ⟨v, ?_⟩
      have := congrArg (fun g : M.obj d ⟶ M.obj f => g.hom v)
        (M.mulList_append l₁ l₂ d e f hl₁ hl₂ (by
          simp only [List.length_append, Nat.cast_add]; omega))
      simpa using this
    · simp
    · intro a b ha hb; simpa [map_add] using Submodule.add_mem _ ha hb
  · simp
  · intro a b ha hb; exact Submodule.add_mem _ ha hb

/-- Functoriality of `quotL`: a morphism `f : A ⟶ B` induces `A/LA ⟶ B/LB`. -/
noncomputable def quotLMap {A B : GradedModule k n} (f : A ⟶ B) (c : Fin (n + 1) → k) :
    A.quotL c ⟶ B.quotL c where
  app d := ModuleCat.ofHom (Submodule.mapQ _ _ (f.app d).hom (by
    rintro x ⟨y, rfl⟩
    exact ⟨(f.app (d + -1)).hom y, congrArg (fun g : A.obj (d + -1) ⟶ B.obj d => g.hom y)
      (comm_mulL f c (d + -1) d (by ring))⟩))
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext ?_)
    rintro ⟨x⟩
    exact congrArg (Submodule.Quotient.mk (p := LinearMap.range ((B.mulLHom c).app (d + 1)).hom))
      (congrArg (fun g : A.obj d ⟶ B.obj (d + 1) => g.hom x) (f.comm i d))

lemma quotLMap_mk {A B : GradedModule k n} (f : A ⟶ B) (c : Fin (n + 1) → k) (d : ℤ)
    (x : A.obj d) :
    ((quotLMap f c).app d).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((f.app d).hom x) := rfl

/-- Forget the action of a variable, on morphisms. -/
def dropVarMap {A B : GradedModule k (n + 1)} (f : A ⟶ B) (j : Fin (n + 2)) :
    A.dropVar j ⟶ B.dropVar j where
  app d := f.app d
  comm i d := f.comm (j.succAbove i) d

/-- Functoriality of restriction to a hyperplane. -/
noncomputable def restrictLMap {A B : GradedModule k (n + 1)} (f : A ⟶ B) (c : Fin (n + 2) → k)
    (j : Fin (n + 2)) : A.restrictL c j ⟶ B.restrictL c j :=
  dropVarMap (quotLMap f c) j

/-- If multiplication by `L` is injective on `B` and `f : A ⟶ B` is degreewise injective, then
multiplication by `L` is injective on `A`. -/
lemma injective_mulLHom_of_injective {A B : GradedModule k n} (c : Fin (n + 1) → k) (f : A ⟶ B)
    (hf : ∀ d, Function.Injective (f.app d).hom)
    (hB : ∀ d, Function.Injective ((B.mulLHom c).app d).hom) :
    ∀ d, Function.Injective ((A.mulLHom c).app d).hom := by
  intro d x y hxy
  have e1 : ∀ z : A.obj (d + -1), ((B.mulLHom c).app d).hom ((f.app (d + -1)).hom z)
      = (f.app d).hom (((A.mulLHom c).app d).hom z) := fun z =>
    congrArg (fun g : A.obj (d + -1) ⟶ B.obj d => g.hom z) (comm_mulL f c (d + -1) d (by ring))
  refine hf (d + -1) (hB d ?_)
  rw [e1, e1, hxy]

/-- If `0 → A → B → Q → 0` is short exact and multiplication by the linear form `L` is
injective on `Q`, then the restricted sequence `0 → A/LA → B/LB → Q/LQ → 0` is short exact.
This is the vanishing of `Tor₁(𝒪_H, Q)` used in the proof of Theorem 2.3.8. -/
lemma shortExact_quotLMap {A B Q : GradedModule k n} {f : A ⟶ B} {g : B ⟶ Q}
    (hfg : ShortExact f g) (c : Fin (n + 1) → k)
    (hQ : ∀ d, Function.Injective ((Q.mulLHom c).app d).hom) :
    ShortExact (quotLMap f c) (quotLMap g c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective
      (LinearMap.range ((A.mulLHom c).app d).hom) x
    rw [quotLMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨b, hb⟩ := hx
    -- `g b` is killed by `L`, hence `b` lies in the image of `f`
    have hgb : ((Q.mulLHom c).app d).hom ((g.app (d + -1)).hom b) = 0 := by
      have e1 : ((Q.mulLHom c).app d).hom ((g.app (d + -1)).hom b)
          = (g.app d).hom (((B.mulLHom c).app d).hom b) :=
        congrArg (fun k' : B.obj (d + -1) ⟶ Q.obj d => k'.hom b)
          (comm_mulL g c (d + -1) d (by ring))
      rw [e1, hb]
      have : (f.app d).hom a ∈ LinearMap.range (f.app d).hom := LinearMap.mem_range_self _ _
      rw [hfg.exact d] at this
      exact this
    have hgb0 : (g.app (d + -1)).hom b = 0 :=
      (injective_iff_map_eq_zero _).mp (hQ d) _ hgb
    have hbmem : b ∈ LinearMap.range (f.app (d + -1)).hom := by
      rw [hfg.exact (d + -1)]
      exact LinearMap.mem_ker.mpr hgb0
    obtain ⟨a', rfl⟩ := hbmem
    have : (f.app d).hom (((A.mulLHom c).app d).hom a') = (f.app d).hom a := by
      refine Eq.trans ?_ hb
      exact (congrArg (fun k' : A.obj (d + -1) ⟶ B.obj d => k'.hom a')
        (comm_mulL f c (d + -1) d (by ring))).symm
    have ha : ((A.mulLHom c).app d).hom a' = a := hfg.injective d this
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨a', ha⟩
  · intro d
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective
        (LinearMap.range ((A.mulLHom c).app d).hom) y
      rw [LinearMap.mem_ker, quotLMap_mk, quotLMap_mk, Submodule.Quotient.mk_eq_zero]
      have : (g.app d).hom ((f.app d).hom a) = 0 := by
        have : (f.app d).hom a ∈ LinearMap.range (f.app d).hom := LinearMap.mem_range_self _ _
        rw [hfg.exact d] at this
        exact this
      rw [this]
      exact Submodule.zero_mem _
    · intro x hx
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective
        (LinearMap.range ((B.mulLHom c).app d).hom) x
      rw [LinearMap.mem_ker, quotLMap_mk, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨q, hq⟩ := hx
      obtain ⟨b', rfl⟩ := hfg.surjective (d + -1) q
      have : (g.app d).hom (b - ((B.mulLHom c).app d).hom b') = 0 := by
        have e1 : (g.app d).hom (((B.mulLHom c).app d).hom b')
            = ((Q.mulLHom c).app d).hom ((g.app (d + -1)).hom b') :=
          (congrArg (fun k' : B.obj (d + -1) ⟶ Q.obj d => k'.hom b')
            (comm_mulL g c (d + -1) d (by ring))).symm
        rw [map_sub, e1, hq, sub_self]
      have hmem : b - ((B.mulLHom c).app d).hom b' ∈ LinearMap.range (f.app d).hom := by
        rw [hfg.exact d]; exact LinearMap.mem_ker.mpr this
      obtain ⟨a, ha⟩ := hmem
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      rw [quotLMap_mk, ha]
      refine (Submodule.Quotient.eq _).mpr ?_
      have hb'' : -((B.mulLHom c).app d).hom b' ∈ LinearMap.range ((B.mulLHom c).app d).hom :=
        neg_mem (LinearMap.mem_range_self _ b')
      simpa only [sub_sub_cancel_left] using hb''
  · intro d x
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective
      (LinearMap.range ((Q.mulLHom c).app d).hom) x
    obtain ⟨b, rfl⟩ := hfg.surjective d q
    exact ⟨Submodule.Quotient.mk b, rfl⟩

/-- An isomorphism of graded modules is degreewise an isomorphism. -/
@[simps] def isoApp {M N : GradedModule k n} (e : M ≅ N) (d : ℤ) : M.obj d ≅ N.obj d where
  hom := e.hom.app d
  inv := e.inv.app d
  hom_inv_id := by rw [← comp_app, e.hom_inv_id, id_app]
  inv_hom_id := by rw [← comp_app, e.inv_hom_id, id_app]

lemma comm_mulList {M N : GradedModule k n} (f : M ⟶ N) :
    ∀ (l : List (Fin (n + 1))) (d e : ℤ) (h : d + (l.length : ℤ) = e),
      f.app d ≫ N.mulList l d e h = M.mulList l d e h ≫ f.app e
  | [], d, e, h => by
      have hde : d = e := by simpa using h
      subst hde
      simp [mulList]
  | i :: t, d, e, h => by
      have h' : d + 1 + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega
      simp only [mulList, Category.assoc, ← comm_mulList f t (d + 1) e h']
      rw [← Category.assoc, f.comm i d, Category.assoc]

/-- If `f : M ⟶ N` is degreewise surjective and the multiplication maps out of degree `d`
span `M` in degree `e`, then they span `N` in degree `e`. -/
lemma mulSpan_eq_top_of_surjective {M N : GradedModule k n} (f : M ⟶ N)
    (hf : ∀ d, Function.Surjective (f.app d).hom) (d e : ℤ) (h : M.mulSpan d e = ⊤) :
    N.mulSpan d e = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨x, rfl⟩ := hf e y
  have hx : x ∈ M.mulSpan d e := h ▸ Submodule.mem_top
  refine Submodule.iSup_induction _
    (motive := fun z => (f.app e).hom z ∈ N.mulSpan d e) hx ?_ ?_ ?_
  · rintro ⟨l, hl⟩ z ⟨w, rfl⟩
    refine le_mulSpan N d e l hl ⟨(f.app d).hom w, ?_⟩
    exact congrArg (fun g : M.obj d ⟶ N.obj e => g.hom w) (comm_mulList f l d e hl)
  · simp
  · intro a b ha hb; simpa [map_add] using Submodule.add_mem _ ha hb

lemma mulSpan_eq_top_of_iso {M N : GradedModule k n} (e : M ≅ N) (d f : ℤ)
    (h : M.mulSpan d f = ⊤) : N.mulSpan d f = ⊤ :=
  mulSpan_eq_top_of_surjective e.hom
    (fun d => (isoApp e d).toLinearEquiv.surjective) d f h

lemma mulList_singleton (M : GradedModule k n) (i : Fin (n + 1)) (d e : ℤ)
    (h : d + ([i].length : ℤ) = e) : M.mulList [i] d e h = M.mulX' i d e (by simpa using h) := by
  simp only [mulList, mulX']

lemma mulSpan_self (M : GradedModule k n) (d : ℤ) : M.mulSpan d d = ⊤ := by
  refine eq_top_iff.mpr (le_trans ?_ (le_mulSpan M d d [] (by simp)))
  rintro x -
  refine ⟨x, ?_⟩
  simp [mulList]

lemma mulL_apply (M : GradedModule k n) (c : Fin (n + 1) → k) (d e : ℤ) (h : d + 1 = e)
    (x : M.obj d) : (M.mulL c d e h).hom x = ∑ i, c i • (M.mulX' i d e h).hom x := by
  simp [mulL]

lemma range_mulX'_le_mulSpan (M : GradedModule k n) (i : Fin (n + 1)) (d e : ℤ) (h : d + 1 = e) :
    LinearMap.range (M.mulX' i d e h).hom ≤ M.mulSpan d e := by
  rintro y ⟨x, rfl⟩
  refine le_mulSpan M d e [i] (by simpa using h) ⟨x, ?_⟩
  rw [mulList_singleton]

lemma range_mulL_le_mulSpan (M : GradedModule k n) (c : Fin (n + 1) → k) (d e : ℤ)
    (h : d + 1 = e) : LinearMap.range (M.mulL c d e h).hom ≤ M.mulSpan d e := by
  rintro y ⟨x, rfl⟩
  rw [mulL_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (range_mulX'_le_mulSpan M i d e h ⟨x, rfl⟩)

lemma dropVar_mulList (N : GradedModule k (n + 1)) (j : Fin (n + 2)) :
    ∀ (l : List (Fin (n + 1))) (d e : ℤ) (h : d + (l.length : ℤ) = e),
      (N.dropVar j).mulList l d e h = N.mulList (l.map j.succAbove) d e (by simpa using h)
  | [], _, _, _ => rfl
  | i :: t, d, e, h => by
      have h' : d + 1 + (t.length : ℤ) = e := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega
      exact congrArg (fun g : N.obj (d + 1) ⟶ N.obj e => N.mulX (j.succAbove i) d ≫ g)
        (dropVar_mulList N j t (d + 1) e h')

lemma dropVar_mulSpan_le (N : GradedModule k (n + 1)) (j : Fin (n + 2)) (d e : ℤ) :
    (N.dropVar j).mulSpan d e ≤ N.mulSpan d e := by
  refine iSup_le ?_
  rintro ⟨l, hl⟩
  rw [dropVar_mulList N j l d e hl]
  exact le_mulSpan N d e (l.map j.succAbove) (by simpa using hl)

/-- If `f : M ⟶ N` is surjective in degree `d`, the multiplication span of `N` out of degree
`d` is contained in the image of that of `M`. -/
lemma mulSpan_le_map {M N : GradedModule k n} (f : M ⟶ N) (d e : ℤ)
    (hf : Function.Surjective (f.app d).hom) :
    N.mulSpan d e ≤ Submodule.map (f.app e).hom (M.mulSpan d e) := by
  refine iSup_le ?_
  rintro ⟨l, hl⟩ y ⟨w, rfl⟩
  obtain ⟨z, rfl⟩ := hf w
  exact ⟨(M.mulList l d e hl).hom z, le_mulSpan M d e l hl ⟨z, rfl⟩,
    (congrArg (fun g : M.obj d ⟶ N.obj e => g.hom z) (comm_mulList f l d e hl)).symm⟩

lemma structureModule_mulX'_val (i : Fin (n + 1)) (a b : ℤ) (h : a + 1 = b)
    (p : (structureModule k n).obj a) :
    (((structureModule k n).mulX' i a b h).hom p).1 = MvPolynomial.X i * p.1 := by
  subst h
  simp [mulX', structureModule, polyMulX]

lemma mul_mem_polySubmodule {q : MvPolynomial (Fin (n + 1)) k} {e : ℕ}
    (hq : q ∈ polySubmodule k n e) {d : ℤ} {p : MvPolynomial (Fin (n + 1)) k}
    (hp : p ∈ polySubmodule k n (d + -(e : ℤ))) : q * p ∈ polySubmodule k n d := by
  rcases lt_or_ge (d + -(e : ℤ)) 0 with hd | hd
  · rw [polySubmodule_of_neg k n hd, Submodule.mem_bot] at hp
    subst hp
    simp
  · rw [polySubmodule_of_nonneg k n hd] at hp
    rw [polySubmodule_of_nonneg k n (by omega), MvPolynomial.mem_homogeneousSubmodule]
    have hdeg : d.toNat = e + (d + -(e : ℤ)).toNat := by omega
    rw [hdeg]
    exact ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hq).mul hp

/-- Multiplication by a homogeneous polynomial `q` of degree `e`, on the graded pieces of
`S = k[x₀, …, x_n]`. -/
noncomputable def polyMulPoly {q : MvPolynomial (Fin (n + 1)) k} {e : ℕ}
    (hq : q ∈ polySubmodule k n e) (d : ℤ) :
    ↥(polySubmodule k n (d + -(e : ℤ))) →ₗ[k] ↥(polySubmodule k n d) where
  toFun p := ⟨q * p.1, mul_mem_polySubmodule hq p.2⟩
  map_add' p p' := Subtype.ext (by simpa using mul_add _ _ _)
  map_smul' a p := Subtype.ext (by simp)

@[simp] lemma polyMulPoly_val {q : MvPolynomial (Fin (n + 1)) k} {e : ℕ}
    (hq : q ∈ polySubmodule k n e) (d : ℤ) (p : ↥(polySubmodule k n (d + -(e : ℤ)))) :
    (polyMulPoly hq d p).1 = q * p.1 := rfl

/-- Multiplication by a homogeneous polynomial `q` of degree `e`, as a morphism
`𝒪(-e) → 𝒪` of graded modules on `ℙⁿ`; its cokernel is the structure sheaf of the
hypersurface `V(q)`. -/
noncomputable def mulPolyHom {q : MvPolynomial (Fin (n + 1)) k} {e : ℕ}
    (hq : q ∈ polySubmodule k n e) :
    (structureModule k n).twist (-(e : ℤ)) ⟶ structureModule k n where
  app d := ModuleCat.ofHom (polyMulPoly hq d)
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext fun p => Subtype.ext ?_)
    have h1 := structureModule_mulX'_val i d (d + 1) rfl
      ((polyMulPoly hq d p : ↥(polySubmodule k n d)) : (structureModule k n).obj d)
    have h2 := structureModule_mulX'_val i (d + -(e : ℤ)) (d + 1 + -(e : ℤ)) (by ring) p
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      twist_mulX, mulX'_rfl, polyMulPoly_val] at h1 h2 ⊢
    exact h1.trans (Eq.trans (by ring) (congrArg (fun z => q * z) h2).symm)

lemma injective_mulPolyHom_app [IsDomain k] {q : MvPolynomial (Fin (n + 1)) k} {e : ℕ}
    (hq : q ∈ polySubmodule k n e) (hq0 : q ≠ 0) (d : ℤ) :
    Function.Injective ((mulPolyHom hq).app d).hom := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  refine Subtype.ext ?_
  have h : q * p.1 = 0 := congrArg Subtype.val hp
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 hq0
  · simpa using h0

/-- The dimension of the degree-`d` graded piece of `k[x₀, …, x_n]` is `C(n+d, n)`. -/
lemma finrank_polySubmodule {K : Type u} [Field K] (m : ℕ) {d : ℤ} (hd : 0 ≤ d) :
    Module.finrank K (polySubmodule K m d) = ((m : ℤ) + d).toNat.choose m := by
  rw [polySubmodule_of_nonneg K m hd, MvPolynomial.finrank_homogeneousSubmodule_fin]
  congr 1
  omega

/-- A degreewise bijective morphism of graded modules is an isomorphism. -/
noncomputable def isoOfBijective {M N : GradedModule k n} (f : M ⟶ N)
    (hf : ∀ d, Function.Bijective (f.app d).hom) : M ≅ N where
  hom := f
  inv :=
    { app := fun d =>
        ModuleCat.ofHom (LinearEquiv.ofBijective (f.app d).hom (hf d)).symm.toLinearMap
      comm := fun i d => by
        have key : ∀ (D : ℤ) (z : N.obj D),
            (f.app D).hom ((LinearEquiv.ofBijective (f.app D).hom (hf D)).symm z) = z :=
          fun D z => (LinearEquiv.ofBijective (f.app D).hom (hf D)).apply_symm_apply z
        refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
        refine (hf (d + 1)).1 ?_
        have h1 := congrArg (fun g : M.obj d ⟶ N.obj (d + 1) => g.hom
          ((LinearEquiv.ofBijective (f.app d).hom (hf d)).symm y)) (f.comm i d)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
          LinearEquiv.coe_coe] at h1 ⊢
        rw [key, ← h1, key] }
  hom_inv_id := by
    refine hom_ext fun d => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (LinearEquiv.ofBijective (f.app d).hom (hf d)).symm_apply_apply x
  inv_hom_id := by
    refine hom_ext fun d => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    exact (LinearEquiv.ofBijective (f.app d).hom (hf d)).apply_symm_apply y

lemma mulSpan_eq_top_iff_of_bijective {M N : GradedModule k n} (f : M ⟶ N)
    (hf : ∀ d, Function.Bijective (f.app d).hom) (d e : ℤ) :
    M.mulSpan d e = ⊤ ↔ N.mulSpan d e = ⊤ :=
  ⟨mulSpan_eq_top_of_iso (isoOfBijective f hf) d e,
    mulSpan_eq_top_of_iso (isoOfBijective f hf).symm d e⟩

lemma structureModule_mulX_val (i : Fin (n + 1)) (d : ℤ) (p : (structureModule k n).obj d) :
    (((structureModule k n).mulX i d).hom p).1 = MvPolynomial.X i * p.1 := rfl

lemma pow_mulX_apply (M : GradedModule k n) (r : ℕ) (i : Fin (n + 1)) (d : ℤ)
    (x : (M.pow r).obj d) (t : Fin r) :
    ((M.pow r).mulX i d).hom x t = (M.mulX i d).hom (x t) := rfl

lemma pow_mulX'_apply (M : GradedModule k n) (r : ℕ) (i : Fin (n + 1)) (a b : ℤ) (h : a + 1 = b)
    (x : (M.pow r).obj a) (t : Fin r) :
    ((M.pow r).mulX' i a b h).hom x t = (M.mulX' i a b h).hom (x t) := by
  subst h
  simp only [mulX'_rfl]
  rfl

lemma pow_mulL_apply (M : GradedModule k n) (r : ℕ) (c : Fin (n + 1) → k) (a b : ℤ)
    (h : a + 1 = b) (x : (M.pow r).obj a) (t : Fin r) :
    ((M.pow r).mulL c a b h).hom x t = (M.mulL c a b h).hom (x t) := by
  have hproj : ∀ v : (M.pow r).obj b,
      v t = (LinearMap.proj t : ((Fin r) → M.obj b) →ₗ[k] M.obj b) v := fun _ => rfl
  rw [mulL_apply, mulL_apply]
  refine Eq.trans (hproj _) ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  exact congrArg (c i • ·) (pow_mulX'_apply M r i a b h x t)

lemma structureModule_mulL_val (c : Fin (n + 1) → k) (a b : ℤ) (h : a + 1 = b)
    (p : (structureModule k n).obj a) :
    (((structureModule k n).mulL c a b h).hom p).1
      = MvPolynomial.linearForm c * p.1 := by
  have h1 : ((structureModule k n).mulL c a b h).hom p
      = ∑ i, c i • ((structureModule k n).mulX' i a b h).hom p := mulL_apply _ c a b h p
  have h2 : ((∑ i, c i • ((structureModule k n).mulX' i a b h).hom p :
        ↥(polySubmodule k n b)) : MvPolynomial (Fin (n + 1)) k)
      = ∑ i, c i • (((structureModule k n).mulX' i a b h).hom p).1 := by
    rw [show ((∑ i, c i • ((structureModule k n).mulX' i a b h).hom p :
          ↥(polySubmodule k n b)) : MvPolynomial (Fin (n + 1)) k)
        = (polySubmodule k n b).subtype
            (∑ i, c i • ((structureModule k n).mulX' i a b h).hom p) from rfl, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [h1, h2, MvPolynomial.linearForm_def, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [structureModule_mulX'_val i a b h p, MvPolynomial.smul_eq_C_mul]
  ring

/- The obligation `GradedModule.nonempty_restrictL_pow_structureIso` — a hyperplane in `ℙⁿ⁺¹`
is a `ℙⁿ`, i.e. `k[x₀,…,x_{n+1}]/(L) ≅ k[y₀,…,y_n]` for a linear form `L = ∑ cᵢxᵢ` with `c_j` a
unit — was recorded here and is now **discharged**: see
`StacksAndModuli/API/PolynomialHyperplane.lean` for the substitution and its kernel, and
`StacksAndModuli/API/ProjectiveHyperplaneIso.lean` for the resulting isomorphism of graded modules
`GradedModule.nonempty_restrictL_pow_structureIso`. -/

end GradedModule

end AlgebraicGeometry.ProjectiveSpace
