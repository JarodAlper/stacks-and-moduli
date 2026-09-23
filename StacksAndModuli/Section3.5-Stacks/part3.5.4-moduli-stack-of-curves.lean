module

public import StacksAndModuli.«Section3.5-Stacks».«part3.5.3-classifying-stacks-and-quotient-stacks»
public import StacksAndModuli.API.BrauerSeveri
public import StacksAndModuli.API.EllipticGroupFamily

/-!
# Moduli stack of curves

This module follows the subsection "Moduli stack of curves" of §3.5 (Stacks) of
*Stacks and Moduli*, section label
`sec:stacks`.

Main result:
- Faithful supporting models for Exercise 3.5.15: the Brauer--Severi prestack
  and the group-structured elliptic-family prestack, both proved stable under
  arbitrary base change.  The comparison with fiberwise genus and the stack
  assertions require geometric infrastructure not yet available.
- `RmkM1NotAStack`: **Remark 3.5.16** (`rmk:M1-not-a-stack`), retained as prose with
  the section-complete marker permitted for literature-dependent remarks.
-/

@[expose] public section

section RmkM1NotAStack

/-!
**Remark 3.5.16** (`rmk:M1-not-a-stack`): the prestack of smooth proper families of
genus-one curves whose total spaces are schemes is not a stack for the étale topology.
Raynaud's counterexample supplies an étale descent datum whose effective descent is an
algebraic space but not a scheme. If algebraic-space total spaces are allowed instead,
the corresponding prestack is a stack.

This literature-dependent negative example and its algebraic-space refinement are retained
as prose because the required algebraic-space and genus-one-family infrastructure is not
yet present in Mathlib or StacksAndModuli.
-/

-- STATUS: remark-complete

end RmkM1NotAStack
