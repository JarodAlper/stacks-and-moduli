module

public import StacksAndModuli.«Section4.9-Examples».«part4.9.1-examples-of-algebraic-spaces»
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Extremely non-separated examples

This module formalizes Subsection 4.9.4, "Extremely non-separated examples"
(`subsec:examples-non-separated`), of §4.9 (Further examples) of *Stacks and Moduli*,
section label `subsec:examples`. It
covers `ex:non-quasi-separated-algebraic-space` (= `ex:classifying-stack-BZ`, both labels
on Example 4.9.36) together with the unlabeled exercise following it, and
`ex:DM-stack-diagonal-not-separated` (Example 4.9.38).

These examples are counterexamples to properties which hold for algebraic stacks with
quasi-compact and separated diagonal but fail in general (compare Corollary 5.5.8). For
the construction that is within reach, we state that the étale sheafification of
$G = \bA^1/\underline{\bZ}$ is an algebraic space which is not a scheme and whose
diagonal is not quasi-compact.

The classifying stacks $\B \underline{\bZ}$, $\B G$ and $\B Q$ and the group structures
themselves are ledgered: classifying stacks are blocked on principal bundles (Appendix B),
and the group structure on $\coprod_{n \in \bZ} \Spec \bZ$ is blocked on the compatibility
of infinite coproducts of schemes with fiber products (infinite extensivity, a Mathlib
TODO).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section ExNonQuasiSeparatedAlgebraicSpace

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace AffineSpace

variable (n : Type u) (S : Scheme.{u})

/-- Let $S$ be a scheme and $m$ an integer. The coordinatewise translation
$x \mapsto x + m$ of the affine space $\bA(n; S)$ over $S$. -/
noncomputable def intTranslation (m : ℤ) : 𝔸(n; S) ⟶ 𝔸(n; S) :=
  homOfVector (𝔸(n; S) ↘ S) fun i ↦ coord S i + (m : Γ(𝔸(n; S), ⊤))

/-- Translation by the integer $0$ on affine space is the identity. -/
@[simp]
lemma intTranslation_zero : intTranslation n S 0 = 𝟙 𝔸(n; S) := by
  apply hom_ext
  · simp [intTranslation]
  · intro i
    simp [intTranslation]

/-- Integer translations of affine space compose additively:
$(x + m) + m' = x + (m + m')$. -/
@[reassoc]
lemma intTranslation_comp_intTranslation (m m' : ℤ) :
    intTranslation n S m ≫ intTranslation n S m' = intTranslation n S (m + m') := by
  apply hom_ext
  · simp [intTranslation]
  · intro i
    simp [intTranslation, add_assoc]

/- Integer translations of affine space are isomorphisms (translation by `-m` is
inverse). -/
instance (m : ℤ) : IsIso (intTranslation n S m) :=
  ⟨intTranslation n S (-m),
    by rw [intTranslation_comp_intTranslation, add_neg_cancel, intTranslation_zero],
    by rw [intTranslation_comp_intTranslation, neg_add_cancel, intTranslation_zero]⟩

end AffineSpace

variable (S : Scheme.{u})

/- The second projection of the integer-translation relation on the affine line is étale:
every translation is an isomorphism. Registered as an instance (keyed to the specific
defs, so it cannot pollute general instance searches). -/
instance :
    Etale (Scheme.partialEndRelSnd (fun _ : ℤ ↦ (⊤ : (𝔸(PUnit.{u + 1}; S)).Opens))
      (fun m ↦ AffineSpace.intTranslation PUnit.{u + 1} S m)) :=
  Scheme.etale_partialEndRelSnd _ _ fun _ ↦ inferInstance

/-- Background definition used in Example 4.9.36: for a scheme $S$, the quotient
presheaf $\bA^1_S/\underline{\bZ}$ of the action of the constant
group scheme $\underline{\bZ}$ on the affine line by integer translations
$n \cdot x = x + n$: the coequalizer of the two projections
$\coprod_{n \in \bZ} \bA^1 \rightrightarrows \bA^1$, $(n, x) \mapsto x$ and
$(n, x) \mapsto x + n$. Over a characteristic-zero field, its étale sheafification
$G = \bA^1/\underline{\bZ}$ is a quasi-compact, locally noetherian group algebraic space
with non-quasi-compact diagonal which is not a scheme. -/
noncomputable abbrev intTranslationQuotientPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u :=
  Scheme.partialEndQuotientPresheaf (fun _ : ℤ ↦ (⊤ : (𝔸(PUnit.{u + 1}; S)).Opens))
    (fun m ↦ AffineSpace.intTranslation PUnit.{u + 1} S m)

variable {k : Type u} [Field k] [CharZero k]

/-- **Example 4.9.36** (`ex:non-quasi-separated-algebraic-space`) (the quotient is an
algebraic space): let $\kk$ be a field of characteristic zero and let $X$ be an étale
sheafification of the quotient presheaf of the integer-translation action
$n \cdot x = x + n$ of $\underline{\bZ}$ on $\bA^1_{\kk}$. Then
$G = \bA^1/\underline{\bZ}$ is an algebraic space: the translation relation is a
(non-quasi-compact) étale equivalence relation. -/
theorem isAlgebraicSpace_of_isSheafificationHom_intTranslationQuotientPresheaf
    {X : Scheme.{u}ᵒᵖ ⥤ Type u}
    (η : intTranslationQuotientPresheaf (Spec (CommRingCat.of k)) ⟶ X)
    (hη : Presheaf.IsSheafificationHom Scheme.etaleTopology η) :
    IsAlgebraicSpace X := by
  refine ⟨hη.1, ?_⟩
  sorry

/-- **Example 4.9.36** (`ex:non-quasi-separated-algebraic-space`) (the quotient is not a
scheme; also part (a) of the unlabeled exercise following it): let $\kk$ be a field of
characteristic zero and let $X$ be an étale sheafification of the quotient presheaf of
the integer-translation action of $\underline{\bZ}$ on $\bA^1_{\kk}$. Then
$G = \bA^1/\underline{\bZ}$ is not representable by a scheme: the ring of
$\underline{\bZ}$-invariant functions on any non-empty open of $\bA^1$ pulled back from
$G$ consists only of constants. Any *quasi-separated* group algebraic space locally of
finite type over $\kk$ is a scheme (Theorem 5.5.28); this example shows that
quasi-separatedness is necessary. -/
theorem not_isRepresentable_of_isSheafificationHom_intTranslationQuotientPresheaf
    {X : Scheme.{u}ᵒᵖ ⥤ Type u}
    (η : intTranslationQuotientPresheaf (Spec (CommRingCat.of k)) ⟶ X)
    (hη : Presheaf.IsSheafificationHom Scheme.etaleTopology η) :
    ¬ X.IsRepresentable := by
  sorry

omit [CharZero k] in
/-- Supporting geometric statement for Example 4.9.36: the scheme of integer-translation
relations, the disjoint union of one copy of the affine line for each integer, is not
quasi-compact as a topological space. -/
theorem not_compactSpace_intTranslationRelation :
    ¬ CompactSpace
      (Scheme.partialEndRel
        (fun _ : ℤ ↦ (⊤ : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k))).Opens))) := by
  intro hc
  let A : Scheme.{u} := 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k))
  let g : ℤ → Scheme.{u} := fun _ ↦ (⊤ : A.Opens).toScheme
  have hc' : CompactSpace (∐ g : Scheme.{u}) := hc
  have hunion : ⋃ i : ℤ, Set.range (Sigma.ι g i).base = Set.univ :=
    (sigmaOpenCover g).iUnion_range
  obtain ⟨t, ht⟩ := (isCompact_univ (X := (∐ g : Scheme.{u}))).elim_finite_subcover
    (fun i : ℤ ↦ Set.range (Sigma.ι g i).base)
    (fun i ↦ (Sigma.ι g i).opensRange.isOpen) (by rw [hunion])
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset t
  have hAne : ∀ i, Nonempty (g i) := by
    intro i
    dsimp only [g]
    rw [Scheme.Opens.nonempty_iff]
    have hA : Nonempty A := by
      dsimp only [A]
      infer_instance
    obtain ⟨a⟩ := hA
    exact ⟨a, Set.mem_univ a⟩
  obtain ⟨a⟩ := hAne j
  have hx : (Sigma.ι g j).base a ∈ ⋃ i ∈ t, Set.range (Sigma.ι g i).base :=
    ht (Set.mem_univ _)
  obtain ⟨i, hi, y, hy⟩ := by simpa using hx
  have hij : i = j := congrArg Sigma.fst ((sigmaι_eq_iff g i j y a).mp hy)
  exact hj (hij ▸ hi)

omit [CharZero k] in
/-- Supporting geometric statement for Example 4.9.36: the relation morphism
$\coprod_{n \in \bZ} \bA^1 \to \bA^1 \times \bA^1$, sending $(n,x)$ to $(x,x+n)$,
is not quasi-compact. -/
theorem not_quasiCompact_intTranslationRelation :
    ¬ QuasiCompact
      (prod.lift
        (Scheme.partialEndRelFst
          (fun _ : ℤ ↦ (⊤ : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k))).Opens)))
        (Scheme.partialEndRelSnd
          (fun _ : ℤ ↦ (⊤ : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k))).Opens))
          (fun m ↦ AffineSpace.intTranslation PUnit.{u + 1}
            (Spec (CommRingCat.of k)) m))) := by
  intro hqc
  let _ : QuasiCompact
      (prod.lift
        (Scheme.partialEndRelFst
          (fun _ : ℤ ↦ (⊤ : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k))).Opens)))
        (Scheme.partialEndRelSnd
          (fun _ : ℤ ↦ (⊤ : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k))).Opens))
          (fun m ↦ AffineSpace.intTranslation PUnit.{u + 1}
            (Spec (CommRingCat.of k)) m))) := hqc
  let A : Scheme.{u} := 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k))
  let Y : Scheme.{u} := A ⨯ A
  let _ : CompactSpace Y := by
    let hY : IsAffine Y := by
      dsimp only [Y]
      exact IsAffine.of_isPullback (IsPullback.of_hasBinaryProduct' A A)
    exact @Scheme.compactSpace_of_isAffine Y hY
  exact not_compactSpace_intTranslationRelation
    (QuasiCompact.compactSpace_of_compactSpace
      (prod.lift
        (Scheme.partialEndRelFst
          (fun _ : ℤ ↦ (⊤ : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k))).Opens)))
        (Scheme.partialEndRelSnd
          (fun _ : ℤ ↦ (⊤ : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k))).Opens))
          (fun m ↦ AffineSpace.intTranslation PUnit.{u + 1}
            (Spec (CommRingCat.of k)) m))))

/-- **Example 4.9.36** (`ex:non-quasi-separated-algebraic-space`) (the diagonal is not
quasi-compact): let $\kk$ be a field of characteristic zero and let $X$ be an étale
sheafification of the quotient presheaf of the integer-translation action of
$\underline{\bZ}$ on $\bA^1_{\kk}$. Then the diagonal of $G = \bA^1/\underline{\bZ}$ is
not quasi-compact: its base change along $\bA^1 \times \bA^1 \to G \times G$ is the
infinite disjoint union $\coprod_{n \in \bZ} \bA^1$. In particular $G$ is not
quasi-separated. -/
theorem not_presheaf_quasiCompact_diagonal_of_intTranslationQuotientPresheaf
    {X : Scheme.{u}ᵒᵖ ⥤ Type u}
    (η : intTranslationQuotientPresheaf (Spec (CommRingCat.of k)) ⟶ X)
    (hη : Presheaf.IsSheafificationHom Scheme.etaleTopology η) :
    ¬ MorphismProperty.presheaf (@QuasiCompact : MorphismProperty Scheme.{u})
      (prod.lift (𝟙 X) (𝟙 X)) := by
  intro hdiag
  apply not_quasiCompact_intTranslationRelation (k := k)
  sorry

/- LEDGER — part (b) of the unlabeled exercise following **Example 4.9.36**
(`ex:non-quasi-separated-algebraic-space`): the generic point
$\Spec \kk(x) \to \bA^1 \to G$ is fixed by the $\underline{\bZ}$-action, and the
composition $\Spec \kk(x) \to G$ does not factor through a monomorphism $\Spec L \to G$
for any field $L$; that is, the generic point of $G$ has no residue field. Blocked on the
theory of points and residue fields of algebraic spaces. Also ledgered from this example:
the quotient $\bA^1_{\bC}/\underline{\bZ}^2$ for $(a, b) \cdot x = x + a + ib$, whose
analytic quotient is an elliptic curve while the algebraic space quotient is not
quasi-separated and not a scheme (compare Stacks Project tags 02Z7 and 02Z8). -/

end AlgebraicGeometry

end ExNonQuasiSeparatedAlgebraicSpace


section ExClassifyingStackBZ

open CategoryTheory Limits AlgebraicGeometry

universe v u

namespace AlgebraicGeometry

/-- Background construction used in Example 4.9.36: for a scheme $S$ and a type $A$,
the constant
scheme $\coprod_{a \in A} S$ over $S$: the disjoint union of copies of $S$ indexed by
$A$. When $A$ carries a group structure this is the underlying scheme of the constant
group scheme $\underline{A}$ over $S$. -/
noncomputable def Scheme.constant (S : Scheme.{u}) (A : Type v) [Small.{u} A] :
    Scheme.{u} :=
  ∐ fun _ : A ↦ S

/-- Supporting non-quasi-compactness result for Example 4.9.36: the constant scheme
$\underline{\bZ} = \coprod_{n \in \bZ} \Spec \bZ$ over $\Spec \bZ$, which occurs as the
fiber of $\B \underline{\bZ}$, is not quasi-compact: the components form an open cover
with no finite subcover. -/
theorem not_compactSpace_constant_int :
    ¬ CompactSpace (Scheme.constant (Spec (CommRingCat.of (ULift.{u} ℤ))) ℤ) := by
  intro hc
  set S : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℤ)) with hS
  set g : ℤ → Scheme.{u} := fun _ ↦ S with hg
  have hc' : CompactSpace (∐ g : Scheme.{u}) := hc
  have hunion : ⋃ i : ℤ, Set.range (Sigma.ι g i).base = Set.univ :=
    (sigmaOpenCover g).iUnion_range
  obtain ⟨t, ht⟩ := (isCompact_univ (X := (∐ g : Scheme.{u}))).elim_finite_subcover
    (fun i : ℤ ↦ Set.range (Sigma.ι g i).base)
    (fun i ↦ (Sigma.ι g i).opensRange.isOpen) (by rw [hunion])
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset t
  have hSne : Nonempty S := by
    rw [hS]; infer_instance
  obtain ⟨s⟩ := hSne
  have hx : (Sigma.ι g j).base s ∈ ⋃ i ∈ t, Set.range (Sigma.ι g i).base :=
    ht (Set.mem_univ _)
  obtain ⟨i, hi, y, hy⟩ := by simpa using hx
  have hij : i = j := congrArg Sigma.fst ((sigmaι_eq_iff g i j y s).mp hy)
  exact hj (hij ▸ hi)

/- LEDGER — **Example 4.9.36** (`ex:classifying-stack-BZ` =
`ex:non-quasi-separated-algebraic-space`) (remaining content).
- The group structure on `Scheme.constant S ℤ` (componentwise addition of indices) is
  blocked on the compatibility of infinite coproducts of schemes with fiber products
  (infinite extensivity of `Scheme`, a Mathlib TODO); `Mathlib.AlgebraicGeometry.Group.*`
  provides `Grp_Class` in `Over S` but no constant group schemes.
- The classifying stack $\B \underline{\bZ}$ is a smooth algebraic stack of dimension 0
  whose diagonal is not quasi-compact; in particular it is not quasi-separated.
- For $G = \bA^1/\underline{\bZ}$ (constructed at the presheaf level in
  `ExNonQuasiSeparatedAlgebraicSpace` above), the classifying stack $\B G$ is a
  Deligne–Mumford stack whose diagonal $\Delta_{\B G}$ is quasi-compact but whose second
  diagonal $\Delta_{\Delta_{\B G}}$ is not; moreover the diagonal of $\B G$ is not
  representable by schemes.
All classifying stacks are blocked on principal bundles (Appendix B), ledgered since
§3.4/§3.5. -/

end AlgebraicGeometry

end ExClassifyingStackBZ


section ExDMStackDiagonalNotSeparated

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Let $X$ be a scheme and $U \subseteq X$ an open subscheme. The presheaf
$X \cup_U X$ obtained by gluing two copies of $X$ along $U$: the pushout, in presheaves
on $\Sch$, of the two copies of the open immersion $U \to X$. Its étale sheafification is
representable by the glued scheme $X \cup_U X$; for $U \neq X$ dense the glued scheme is
not separated. -/
noncomputable def Scheme.Opens.doublePresheaf (U : X.Opens) : Scheme.{u}ᵒᵖ ⥤ Type u :=
  pushout (yoneda.map U.ι) (yoneda.map U.ι)

/-- Let $X$ be a scheme and $U \subseteq X$ an open subscheme. The morphism
$X \cup_U X \to X$ from the glued presheaf which is the identity on both copies of
$X$. -/
noncomputable def Scheme.Opens.doublePresheafToBase (U : X.Opens) :
    U.doublePresheaf ⟶ yoneda.obj X :=
  pushout.desc (𝟙 _) (𝟙 _) rfl

/-- Supporting representability statement for Example 4.9.38: let $X$ be a scheme,
$U \subseteq X$ an
open subscheme and $G$ an étale sheafification of the glued presheaf $X \cup_U X$. Then
$G$ is representable by a scheme (the gluing of two copies of $X$ along $U$; a Zariski
gluing). -/
theorem Scheme.Opens.isRepresentable_of_isSheafificationHom_doublePresheaf (U : X.Opens)
    {G : Scheme.{u}ᵒᵖ ⥤ Type u} (η : U.doublePresheaf ⟶ G)
    (hη : Presheaf.IsSheafificationHom Scheme.etaleTopology η) :
    G.IsRepresentable := by
  sorry

/-- Background definition used in Example 4.9.38: for a scheme $S$, the non-separated affine line
$Q = \bA^1 \cup_{\bA^1 \setminus 0} \bA^1$ over $S$ at the presheaf level: two copies of
the affine line glued along the complement of the origin. Its étale sheafification is
representable by the non-separated affine line, which is a group scheme over $\bA^1$
(via `AlgebraicGeometry.Scheme.Opens.doublePresheafToBase`) whose fibers are trivial
except over the origin, where the fiber is $\bZ/2$. -/
noncomputable abbrev nonseparatedAffineLinePresheaf (S : Scheme.{u}) :
    Scheme.{u}ᵒᵖ ⥤ Type u :=
  ((𝔸(PUnit.{u + 1}; S)).basicOpen (AffineSpace.coord S PUnit.unit)).doublePresheaf

/- LEDGER — **Example 4.9.38** (`ex:DM-stack-diagonal-not-separated`) (remaining
content).
- The group scheme structure of $Q \to \bA^1$ (a group object in $\Sch/\bA^1$) and the
  classifying stack $\B Q$, a Deligne–Mumford stack with non-separated diagonal: blocked
  on gluing data for the scheme $Q$ itself (or the representability statement above) and
  on classifying stacks (principal bundles, Appendix B).
- The general construction: for a finite étale group scheme $G \to S$ and a subgroup
  scheme $H \subseteq G$ over $S$, the quotient $G/H$ is separated iff $H \subseteq G$ is
  closed, and is a group algebraic space if $H$ is normal. For
  $G = \bZ/2 \times \bA^1 \to \bA^1$ and $H = G \setminus \{(-1, 0)\}$ — the scheme
  underlying the bug-eyed relation `AlgebraicGeometry.bugEyedRelOpens` of part 4.9.1 —
  the quotient $Q = G/H$ is the non-separated affine line over $\bA^1$. Blocked on group
  scheme actions and quotients.
- The twisted form: for $\mu_{3,\bQ} = \Spec \bQ \amalg \Spec \bQ[x]/(x^2+x+1)$ and
  $G = \mu_{3,\bQ} \times \bA^1_{\bQ}$, the quotient $Q = G/H$ is a non-separated étale
  group algebraic space over $\bA^1_{\bQ}$ which is not a scheme (an affine open around
  the non-identity point of $Q_0$ would pull back to an affine open of
  $\bA^1_{\bQ[x]/(x^2+x+1)}$ containing two origins); here $\B Q$ is quasi-compact and
  quasi-separated but its diagonal is neither separated nor representable by schemes.
  Blocked as above.
- (Prose) most algebraic stacks in moduli theory have separated diagonal; an exception is
  the stack of log structures of Olsson. -/

end AlgebraicGeometry

end ExDMStackDiagonalNotSeparated
