module

public import StacksAndModuli.API.ProjectiveGradedH0
public import Mathlib.Data.Finsupp.Basic

/-!
# The Laurent-monomial model of the localizations of `S = k[x₀, …, x_n]`

Supporting API with no Stacks Project counterpart, developed for the computation of the
cohomology of the twisting sheaves on `ℙⁿ_k`.

The localization `S[1/x_l]` at a product of variables has an evident `k`-basis: the
Laurent monomials `x^a`, `a ∈ ℤ^{n+1}`, with `aᵢ ≥ 0` for every variable `xᵢ` not
inverted.  In the sequential-colimit encoding of `GradedModule.loc` this is not
definitional, so this file constructs the comparison map explicitly and identifies its
image.  The point of the model is that under it the Čech face restrictions become
*inclusions of subspaces of one ambient space*, which is what makes the monomial-by-
monomial computation of the cohomology of `𝒪(d)` possible.

Main declarations:
- `GradedModule.polyFinsupp`, a polynomial as a `Finsupp` on exponent vectors;
- `GradedModule.listExp` and `GradedModule.structureModule_mulList_monomial`.
-/

@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {k : Type u} [CommRing k] {n : ℕ}

/-! ## Polynomials as finitely supported functions on exponent vectors -/

/-- A polynomial viewed as a finitely supported function on exponent vectors. -/
def polyFinsupp (p : MvPolynomial (Fin (n + 1)) k) : (Fin (n + 1) →₀ ℕ) →₀ k :=
  Finsupp.onFinset p.support (fun b => coeff b p) (fun _b hb => mem_support_iff.mpr hb)

@[simp] lemma polyFinsupp_apply (p : MvPolynomial (Fin (n + 1)) k)
    (b : Fin (n + 1) →₀ ℕ) : polyFinsupp p b = coeff b p :=
  Finsupp.onFinset_apply

/-- `polyFinsupp` as a `k`-linear map. -/
def polyFinsuppₗ : MvPolynomial (Fin (n + 1)) k →ₗ[k] ((Fin (n + 1) →₀ ℕ) →₀ k) where
  toFun := polyFinsupp
  map_add' _p _q := Finsupp.ext fun b => by
    simp only [polyFinsupp_apply, Finsupp.add_apply, coeff_add]
  map_smul' a p := Finsupp.ext fun b => by
    simp only [polyFinsupp_apply, Finsupp.smul_apply, coeff_smul, RingHom.id_apply,
      smul_eq_mul]

@[simp] lemma polyFinsuppₗ_apply (p : MvPolynomial (Fin (n + 1)) k) :
    polyFinsuppₗ p = polyFinsupp p := rfl

lemma polyFinsupp_injective :
    Function.Injective (polyFinsupp (k := k) (n := n)) := fun p q h =>
  MvPolynomial.ext _ _ fun b => by
    simpa only [polyFinsupp_apply] using congrArg (fun f => f b) h

/-- Multiplying by a monomial translates the exponent vectors. -/
lemma polyFinsupp_monomial_mul (c : Fin (n + 1) →₀ ℕ) (p : MvPolynomial (Fin (n + 1)) k) :
    polyFinsupp (monomial c 1 * p) = Finsupp.mapDomain (fun a => c + a) (polyFinsupp p) := by
  classical
  have hinj : Function.Injective (fun a : Fin (n + 1) →₀ ℕ => c + a) :=
    fun a b hab => by simpa using hab
  refine Finsupp.ext fun b => ?_
  rw [polyFinsupp_apply, coeff_monomial_mul']
  by_cases hcb : c ≤ b
  · have h1 : Finsupp.mapDomain (fun a : Fin (n + 1) →₀ ℕ => c + a) (polyFinsupp p)
        (c + (b - c)) = polyFinsupp p (b - c) := Finsupp.mapDomain_apply hinj _ _
    rw [add_tsub_cancel_of_le hcb] at h1
    simp only [hcb, ↓reduceIte, one_mul, h1, polyFinsupp_apply]
  · have hrange : b ∉ Set.range (fun a : Fin (n + 1) →₀ ℕ => c + a) := by
      rintro ⟨a, rfl⟩
      exact hcb le_self_add
    simp only [hcb, ↓reduceIte, Finsupp.mapDomain_of_notMem_range _ _ hrange]

/-! ## The monomial attached to a list of variables -/

/-- The exponent vector of the monomial `∏_{i ∈ L} xᵢ`. -/
def listExp (L : List (Fin (n + 1))) : Fin (n + 1) →₀ ℕ :=
  (L.map (fun i => Finsupp.single i 1)).sum

@[simp] lemma listExp_nil : listExp (n := n) [] = 0 := rfl

@[simp] lemma listExp_cons (i : Fin (n + 1)) (L : List (Fin (n + 1))) :
    listExp (i :: L) = Finsupp.single i 1 + listExp L := rfl

lemma X_mul_monomial (i : Fin (n + 1)) (c : Fin (n + 1) →₀ ℕ) :
    (X i : MvPolynomial (Fin (n + 1)) k) * monomial c 1 =
      monomial (Finsupp.single i 1 + c) 1 := by
  rw [X, monomial_mul, one_mul]

/-- The product of a list of variables is the corresponding monomial. -/
lemma list_map_X_prod (L : List (Fin (n + 1))) :
    (L.map (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k)).prod
      = monomial (listExp L) 1 := by
  induction L with
  | nil => simp [listExp_nil]
  | cons i t ih => rw [List.map_cons, List.prod_cons, ih, listExp_cons, X_mul_monomial]

/-- Multiplication along a list of variables is multiplication by the corresponding
monomial. -/
lemma structureModule_mulList_monomial (L : List (Fin (n + 1))) (d e : ℤ)
    (h : d + (L.length : ℤ) = e) (x : (structureModule k n).obj d) :
    (((structureModule k n).mulList L d e h).hom x).1 = monomial (listExp L) 1 * x.1 := by
  rw [structureModule_mulList_val k n L d e h x, list_map_X_prod]

/-! ## The exponent vector as a count -/

lemma listExp_eq_zero_of_notMem {L : List (Fin (n + 1))} {i : Fin (n + 1)} (h : i ∉ L) :
    listExp L i = 0 := by
  induction L with
  | nil => simp [listExp]
  | cons j t ih =>
      rw [List.mem_cons, not_or] at h
      have hji : ¬ (j = i) := fun hc => h.1 hc.symm
      rw [listExp_cons, Finsupp.add_apply, ih h.2, add_zero, Finsupp.single_apply]
      simp only [hji, ↓reduceIte]

lemma one_le_listExp_of_mem {L : List (Fin (n + 1))} {i : Fin (n + 1)} (h : i ∈ L) :
    1 ≤ listExp L i := by
  induction L with
  | nil => exact absurd h List.not_mem_nil
  | cons j t ih =>
      rw [listExp_cons, Finsupp.add_apply]
      rcases List.mem_cons.mp h with hj | ht
      · subst hj
        rw [Finsupp.single_eq_same]
        exact Nat.le_add_right 1 _
      · exact le_trans (ih ht) (Nat.le_add_left _ _)

lemma sum_listExp (L : List (Fin (n + 1))) : ∑ i, listExp L i = L.length := by
  induction L with
  | nil => simp [listExp]
  | cons j t ih =>
      have h1 : ∑ i : Fin (n + 1), (Finsupp.single j (1 : ℕ)) i = 1 := by
        rw [Finset.sum_eq_single j
          (fun b _ hb => by
            rw [Finsupp.single_apply]
            simp only [(Ne.symm hb : j ≠ b), ↓reduceIte])
          (fun hc => absurd (Finset.mem_univ j) hc)]
        exact Finsupp.single_eq_same
      simp only [listExp_cons, Finsupp.add_apply, Finset.sum_add_distrib, ih, h1,
        List.length_cons]
      omega

/-! ## Additivity of the exponent vector -/

/-- The exponent vector of a multiset of variables. -/
def msetExp (s : Multiset (Fin (n + 1))) : Fin (n + 1) →₀ ℕ :=
  (s.map (fun i => Finsupp.single i 1)).sum

lemma listExp_eq_msetExp (L : List (Fin (n + 1))) :
    listExp L = msetExp (L : Multiset (Fin (n + 1))) := rfl

lemma msetExp_add (s t : Multiset (Fin (n + 1))) :
    msetExp (s + t) = msetExp s + msetExp t := by
  simp only [msetExp, Multiset.map_add, Multiset.sum_add]

lemma msetExp_nsmul (a : ℕ) (s : Multiset (Fin (n + 1))) :
    msetExp (a • s) = a • msetExp s := by
  induction a with
  | zero => simp [msetExp]
  | succ b ih => rw [succ_nsmul, msetExp_add, ih, succ_nsmul]

lemma listExp_perm {L₁ L₂ : List (Fin (n + 1))} (h : L₁.Perm L₂) :
    listExp L₁ = listExp L₂ := by
  rw [listExp_eq_msetExp, listExp_eq_msetExp, Multiset.coe_eq_coe.mpr h]

lemma listExp_append (L₁ L₂ : List (Fin (n + 1))) :
    listExp (L₁ ++ L₂) = listExp L₁ + listExp L₂ := by
  rw [listExp_eq_msetExp, listExp_eq_msetExp, listExp_eq_msetExp, ← msetExp_add,
    Multiset.coe_add]

lemma listExp_listPow (L : List (Fin (n + 1))) (a : ℕ) :
    listExp (listPow L a) = a • listExp L := by
  rw [listExp_eq_msetExp, listPow_coe, msetExp_nsmul, listExp_eq_msetExp]

/-! ## The comparison with the Laurent-monomial model -/

variable (k n) in
/-- The free `k`-module on Laurent monomials in `x₀, …, x_n`. -/
abbrev LaurentSpace : Type u := (Fin (n + 1) → ℤ) →₀ k

/-- The exponent shift attached to stage `j` of the localization tower at `x_l`: the
stage-`j` element `f` stands for the Laurent expression `f / x_l^j`. -/
def locShift (l : List (Fin (n + 1))) (j : ℕ) (b : Fin (n + 1) →₀ ℕ) :
    Fin (n + 1) → ℤ :=
  fun i => (b i : ℤ) - (j : ℤ) * (listExp l i : ℤ)

lemma locShift_injective (l : List (Fin (n + 1))) (j : ℕ) :
    Function.Injective (locShift (n := n) l j) := by
  intro b b' h
  refine Finsupp.ext fun i => ?_
  have h1 : ((b i : ℤ)) = ((b' i : ℤ)) := by
    have h2 := congrFun h i
    simpa only [locShift, sub_left_inj] using h2
  exact_mod_cast h1

/-- The comparison map at stage `j` of the localization tower at `x_l`. -/
def laurentStage (l : List (Fin (n + 1))) (d : ℤ) (j : ℕ) :
    (structureModule k n).obj (locDeg l d j) ⟶ ModuleCat.of k (LaurentSpace k n) :=
  ModuleCat.ofHom ((Finsupp.lmapDomain k k (locShift l j)).comp
    ((polyFinsuppₗ (k := k) (n := n)).comp (polySubmodule k n (locDeg l d j)).subtype))

lemma laurentStage_apply (l : List (Fin (n + 1))) (d : ℤ) (j : ℕ)
    (x : (structureModule k n).obj (locDeg l d j)) :
    (laurentStage l d j).hom x = Finsupp.mapDomain (locShift l j) (polyFinsupp x.1) := rfl

lemma laurentStage_injective (l : List (Fin (n + 1))) (d : ℤ) (j : ℕ) :
    Function.Injective ((laurentStage (k := k) l d j).hom) := by
  intro x y hxy
  rw [laurentStage_apply, laurentStage_apply] at hxy
  exact Subtype.ext (polyFinsupp_injective
    (Finsupp.mapDomain_injective (locShift_injective l j) hxy))

/-- The comparison maps intertwine multiplication by a monomial with the change of
stage. -/
lemma laurentStage_mulList (l l₂ : List (Fin (n + 1))) (d : ℤ) (j j₂ : ℕ)
    (L : List (Fin (n + 1))) (hdeg : locDeg l d j + (L.length : ℤ) = locDeg l₂ d j₂)
    (hexp : ∀ i, (listExp L i : ℤ) + (j : ℤ) * (listExp l i : ℤ)
      = (j₂ : ℤ) * (listExp l₂ i : ℤ))
    (x : (structureModule k n).obj (locDeg l d j)) :
    (laurentStage l₂ d j₂).hom
        (((structureModule k n).mulList L _ _ hdeg).hom x) = (laurentStage l d j).hom x := by
  rw [laurentStage_apply, laurentStage_apply, structureModule_mulList_monomial,
    polyFinsupp_monomial_mul, ← Finsupp.mapDomain_comp]
  congr 1
  funext b
  funext i
  simp only [Function.comp_apply, locShift, Finsupp.add_apply, Nat.cast_add]
  rw [← hexp i]
  ring

/-! ## The comparison map on the localization -/

/-- **The Laurent-monomial comparison map.**  Every element of `S[1/x_l]_d` is a finite
`k`-combination of Laurent monomials of degree `d`. -/
def laurent (l : List (Fin (n + 1))) (d : ℤ) :
    ((structureModule k n).loc l).obj d ⟶ ModuleCat.of k (LaurentSpace k n) :=
  ModuleCat.ofHom (Module.DirectLimit.lift k ℕ
    (fun j : ℕ => (structureModule k n).obj (locDeg l d j))
    (fun j j' h => ((structureModule k n).locTr l d j j' h).hom)
    (fun j => (laurentStage l d j).hom)
    (fun j j' hjj' x => by
      refine laurentStage_mulList l l d j j' (listPow l (j' - j)) _ (fun i => ?_) x
      rw [listExp_listPow, Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul,
        Nat.cast_sub hjj']
      ring))

lemma locIncl_laurent (l : List (Fin (n + 1))) (d : ℤ) (j : ℕ) :
    (structureModule k n).locIncl l d j ≫ laurent l d = laurentStage l d j := by
  refine ModuleCat.hom_ext ?_
  refine LinearMap.ext fun x => ?_
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, laurent, locIncl,
    ModuleCat.hom_ofHom]
  exact Module.DirectLimit.lift_of _ _ _

lemma laurent_locIncl (l : List (Fin (n + 1))) (d : ℤ) (j : ℕ)
    (x : (structureModule k n).obj (locDeg l d j)) :
    (laurent l d).hom (((structureModule k n).locIncl l d j).hom x)
      = (laurentStage l d j).hom x := by
  have h := congrArg ModuleCat.Hom.hom (locIncl_laurent (k := k) l d j)
  rw [ModuleCat.hom_comp] at h
  exact LinearMap.congr_fun h x

/-- The comparison map is injective: a localized section is determined by its Laurent
coefficients. -/
lemma laurent_injective (l : List (Fin (n + 1))) (d : ℤ) :
    Function.Injective ((laurent (k := k) l d).hom) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨j, x, hx⟩ := (structureModule k n).locIncl_exists l d z
  subst hx
  rw [laurent_locIncl] at hz
  have hx0 : x = 0 := laurentStage_injective l d j (by rw [hz, map_zero])
  rw [hx0, map_zero]

/-- Under the comparison map the Čech face restrictions become inclusions: a section
localized at `x_l` has the same Laurent expansion after inverting more variables. -/
lemma laurent_locRes {l l' m : List (Fin (n + 1))} (hp : l'.Perm (l ++ m)) (d : ℤ) :
    ((structureModule k n).locRes l hp).app d ≫ laurent l' d = laurent l d := by
  have hl' : listExp l' = listExp l + listExp m := by
    rw [listExp_perm hp, listExp_append]
  refine (structureModule k n).loc_hom_ext l (fun j => ?_)
  rw [← Category.assoc, locIncl_locRes_app, Category.assoc, locIncl_laurent,
    locIncl_laurent]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine laurentStage_mulList l l' d j j (listPow m j) _ (fun i => ?_) x
  rw [listExp_listPow, Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul, hl',
    Finsupp.add_apply, Nat.cast_add]
  ring

lemma laurent_locRes_apply {l l' m : List (Fin (n + 1))} (hp : l'.Perm (l ++ m)) (d : ℤ)
    (z : ((structureModule k n).loc l).obj d) :
    (laurent l' d).hom ((((structureModule k n).locRes l hp).app d).hom z)
      = (laurent l d).hom z := by
  have h := congrArg ModuleCat.Hom.hom (laurent_locRes (k := k) hp d)
  rw [ModuleCat.hom_comp] at h
  exact LinearMap.congr_fun h z

/-! ## The image of the comparison map -/

lemma sum_univ_eq_degree (b : Fin (n + 1) →₀ ℕ) : ∑ i, b i = b.degree :=
  (Finsupp.degree_eq_sum b).symm

lemma sum_univ_eq_weight (b : Fin (n + 1) →₀ ℕ) :
    ∑ i, b i = Finsupp.weight (1 : Fin (n + 1) → ℕ) b := by
  rw [sum_univ_eq_degree, Finsupp.degree_eq_weight_one]
  congr 1

/-- Every monomial occurring in a homogeneous form has the expected total degree. -/
lemma polySubmodule_sum_eq {e : ℤ} {p : MvPolynomial (Fin (n + 1)) k}
    (hp : p ∈ polySubmodule k n e) {b : Fin (n + 1) →₀ ℕ} (hb : coeff b p ≠ 0) :
    ((∑ i, b i : ℕ) : ℤ) = e := by
  rcases lt_or_ge e 0 with he | he
  · rw [polySubmodule_of_neg k n he, Submodule.mem_bot] at hp
    subst hp
    exact absurd (coeff_zero b) hb
  · rw [polySubmodule_of_nonneg k n he, MvPolynomial.mem_homogeneousSubmodule] at hp
    rw [sum_univ_eq_weight, hp hb, Int.toNat_of_nonneg he]

lemma polyFinsupp_monomial (b : Fin (n + 1) →₀ ℕ) (r : k) :
    polyFinsupp (monomial b r) = Finsupp.single b r := by
  refine Finsupp.ext fun c => ?_
  rw [polyFinsupp_apply, coeff_monomial, Finsupp.single_apply]

/-- The degree of a Laurent exponent vector. -/
def lexpDeg (a : Fin (n + 1) → ℤ) : ℤ := ∑ i, a i

/-- The Laurent monomials of degree `d` that are regular away from the variables in `l`:
the natural `k`-basis of the degree-`d` piece of `S[1/x_l]`. -/
def lexpAdm (l : List (Fin (n + 1))) (d : ℤ) : Set (Fin (n + 1) → ℤ) :=
  {a | lexpDeg a = d ∧ ∀ i ∉ l, 0 ≤ a i}

variable (k) in
/-- The Laurent-monomial model of the degree-`d` piece of `S[1/x_l]`. -/
def laurentPiece (l : List (Fin (n + 1))) (d : ℤ) : Submodule k (LaurentSpace k n) :=
  Finsupp.supported k k (lexpAdm l d)

lemma laurentStage_mem (l : List (Fin (n + 1))) (d : ℤ) (j : ℕ)
    (x : (structureModule k n).obj (locDeg l d j)) :
    (laurentStage l d j).hom x ∈ laurentPiece k l d := by
  classical
  rw [laurentStage_apply, laurentPiece, Finsupp.mem_supported]
  intro a ha
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  have hcoeff : coeff b x.1 ≠ 0 := by
    have := Finsupp.mem_support_iff.mp hb
    rwa [polyFinsupp_apply] at this
  have hsum : ((∑ i, b i : ℕ) : ℤ) = locDeg l d j := polySubmodule_sum_eq x.2 hcoeff
  subst hba
  refine ⟨?_, fun i hi => ?_⟩
  · have hd : lexpDeg (locShift l j b)
        = ((∑ i, b i : ℕ) : ℤ) - (j : ℤ) * ((∑ i, listExp l i : ℕ) : ℤ) := by
      simp only [lexpDeg, locShift, Finset.sum_sub_distrib, Nat.cast_sum,
        ← Finset.mul_sum]
    rw [hd, hsum, sum_listExp, locDeg_def]
    ring
  · simp only [locShift, listExp_eq_zero_of_notMem hi, Nat.cast_zero, mul_zero, sub_zero]
    exact Int.natCast_nonneg _

lemma laurent_mem (l : List (Fin (n + 1))) (d : ℤ)
    (z : ((structureModule k n).loc l).obj d) :
    (laurent l d).hom z ∈ laurentPiece k l d := by
  obtain ⟨j, x, hx⟩ := (structureModule k n).locIncl_exists l d z
  subst hx
  rw [laurent_locIncl]
  exact laurentStage_mem l d j x

/-- Every admissible Laurent monomial is realized: it is `x^{a + j·x_l} / x_l^j` for `j`
large. -/
lemma single_mem_range_laurent (l : List (Fin (n + 1))) (d : ℤ) {a : Fin (n + 1) → ℤ}
    (ha : a ∈ lexpAdm l d) :
    Finsupp.single a (1 : k) ∈ LinearMap.range ((laurent (k := k) l d).hom) := by
  classical
  obtain ⟨hdeg, hreg⟩ := ha
  set j : ℕ := Finset.univ.sup (fun i : Fin (n + 1) => (-(a i)).toNat) with hj
  have hnn : ∀ i, 0 ≤ a i + (j : ℤ) * (listExp l i : ℤ) := by
    intro i
    by_cases hi : i ∈ l
    · have h1 : (1 : ℤ) ≤ (listExp l i : ℤ) := by exact_mod_cast one_le_listExp_of_mem hi
      have h2 : (-(a i)).toNat ≤ j :=
        Finset.le_sup (f := fun i : Fin (n + 1) => (-(a i)).toNat) (Finset.mem_univ i)
      have h3 : -(a i) ≤ (j : ℤ) := le_trans (Int.self_le_toNat _) (by exact_mod_cast h2)
      have h4 : (j : ℤ) * 1 ≤ (j : ℤ) * (listExp l i : ℤ) :=
        mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg j)
      omega
    · rw [listExp_eq_zero_of_notMem hi]
      simpa using hreg i hi
  set b : Fin (n + 1) →₀ ℕ :=
    Finsupp.onFinset Finset.univ (fun i => (a i + (j : ℤ) * (listExp l i : ℤ)).toNat)
      (fun _ _ => Finset.mem_univ _) with hb
  have hbapp : ∀ i, ((b i : ℕ) : ℤ) = a i + (j : ℤ) * (listExp l i : ℤ) := by
    intro i
    rw [hb, Finsupp.onFinset_apply, Int.toNat_of_nonneg (hnn i)]
  have hsum : ((∑ i, b i : ℕ) : ℤ) = locDeg l d j := by
    rw [Nat.cast_sum, Finset.sum_congr rfl (fun i _ => hbapp i), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Nat.cast_sum, sum_listExp, locDeg_def]
    exact congrArg₂ (· + ·) hdeg rfl
  have hdeg0 : 0 ≤ locDeg l d j := by rw [← hsum]; exact Int.natCast_nonneg _
  have hp : (monomial b (1 : k)) ∈ polySubmodule k n (locDeg l d j) := by
    rw [polySubmodule_of_nonneg k n hdeg0, MvPolynomial.mem_homogeneousSubmodule]
    refine isHomogeneous_monomial 1 ?_
    rw [← sum_univ_eq_degree]
    omega
  refine ⟨((structureModule k n).locIncl l d j).hom ⟨monomial b (1 : k), hp⟩, ?_⟩
  rw [laurent_locIncl, laurentStage_apply]
  change Finsupp.mapDomain (locShift l j) (polyFinsupp (monomial b (1 : k))) = _
  rw [polyFinsupp_monomial, Finsupp.mapDomain_single]
  congr 1
  funext i
  rw [locShift, hbapp i]
  ring

/-- **The Laurent model.**  The degree-`d` piece of `S[1/x_l]` is freely spanned by the
Laurent monomials of degree `d` that are regular away from `x_l`. -/
theorem range_laurent (l : List (Fin (n + 1))) (d : ℤ) :
    LinearMap.range ((laurent (k := k) l d).hom) = laurentPiece k l d := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    exact laurent_mem l d z
  · rw [laurentPiece, Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact single_mem_range_laurent l d ha

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
