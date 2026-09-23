# Stacks and Moduli in Lean

A Lean 4 formalization of definitions and results from the book draft
*Stacks and Moduli* by Jarod Alper
(<https://sites.math.washington.edu/~jarod/moduli.pdf>), built on
[Mathlib](https://github.com/leanprover-community/mathlib4).

The aim is to state every labelled definition, lemma, proposition, theorem, and corollary
of the book faithfully, with the same hypotheses and conclusions at the book's level of
generality, and to prove as many of them as possible. Examples and exercises are included
where they are used later in the book or are easy to state. This is work in progress and was
written entirely by AI coding agents with very little supervision, so expect
misformalizations.

## Layout

- `StacksAndModuli/` mirrors the book. Each section of the book has one folder, for example
  `StacksAndModuli/Section3.1-Descent/`, whose part files follow the section in order. Each
  section and chapter also has an umbrella module (`StacksAndModuli/Section3.1-Descent.lean`,
  `StacksAndModuli/Chapter3.lean`), and `StacksAndModuli.lean` imports every chapter.
- `StacksAndModuli/API/` and `StacksAndModuli/Util/` hold reusable supporting material that is not tied
  to a single statement of the book.
- `StacksAndModuli/mwe/` is a small self-contained excerpt showing the definitions of algebraic
  spaces and stacks and of the moduli stack of curves.
- `stacks-project-lean/` formalizes results that the book cites from the
  [Stacks Project](https://stacks.math.columbia.edu), one file per tag, organized as
  `StacksProject/<Chapter>/<Section>/<label>.lean`. See its
  [README](stacks-project-lean/README.md) for attribution.

## Coverage

Sections currently represented: 2.1 to 2.5, 3.1 to 3.5, 4.1 to 4.9, 6.1 to 6.5, A.4, and A.6.

A declaration whose docstring opens with the book's number and label, such as
**Proposition 3.1.1** (`prop:descent-modules`), is the designated faithful statement of
that result. Everything else in a file is supporting material: preparatory definitions,
proof lemmas, and API. Numbering follows the draft of the book the library was written
against and may drift as the book is revised; the LaTeX label is the stable key.

Some docstrings refer to internal STATUS, COMMENTARY, and INSIGHTS notes that tracked
progress and formalization decisions during development. Those notes and the book's
LaTeX sources are not part of this repository.

## Building

The Lean toolchain is pinned in `lean-toolchain` and Mathlib in `lake-manifest.json`.

```
lake exe cache get   # download prebuilt Mathlib
lake build           # builds the `StacksAndModuli` and `StacksProject` targets
```

## License

The Lean code is released under the Apache License 2.0; see [LICENSE](LICENSE).
Statements quoted or paraphrased from the Stacks Project in `stacks-project-lean/` are
under the GNU Free Documentation License 1.2 or later, as described in
[stacks-project-lean/README.md](stacks-project-lean/README.md).
