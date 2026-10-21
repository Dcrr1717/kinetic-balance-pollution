# Machine-checked lemmas (Lean 4 + Mathlib)

`FiberLemmas.lean` contains machine-verified proofs of the core
algebraic identities of the paper, as identities **over the reals**.
No statement about matrices, projectors, operator norms or spectra is
formalized: where the paper's proof reduces such a statement to a
scalar identity, it is that scalar identity which is checked.

`SCOPE.md` in this folder is the authoritative inventory — it lists
every declaration and, just as importantly, everything the paper
claims that is *not* formalized. The table below is only a summary and
must not be read as claiming more.

| Lean theorem | What is actually proved | Paper statement |
|---|---|---|
| `key_identity` | t − ρ = 4t³/(1+w)², with w = √(1+4t²), ρ = 2t/(1+w) | Eq. (key), proof of Thm 3.1 |
| `rho_lt` | ρ < t for t > 0 | sign resolution in Thm 3.1 |
| `l_spl_eq` | ℓ(u_spl) = ρ/√(1+ρ²) | Eq. (lspl), Thm 3.1 |
| `l_bal_eq_l_pos` | the balanced and positronic leakages are absolute values of opposite numbers, hence equal | Eq. (lbal), Thm 3.1 |
| `l_anti_eq` | ℓ(u_anti) = (t+ρ)/√((1+ρ²)(1+t²)) | Eq. (lanti), Thm 3.1 |
| `fiber_pythagoras` | ⟨v₊,b⟩² + ⟨v₋,b⟩² = ‖b‖² in the fiber, i.e. g² = 1 − ℓ² | proof step of Thm 4.1 |
| `defect_identity` | the **scalar polynomial identity** g²(1 − 2g² + g²) = g²(1−g²), closed by `ring` — *not* a statement about ‖(I−bbᵀ)Λ₊b‖² | proof step of Thm 4.1 |
| `bal_above_gap` | R_bal − c² = 2c²t²/(1+t²) | Thm 5.1(a) |
| `bal_above_gap_nonneg` | R_bal − c² ≥ 0 | Thm 5.1(a) |
| `anti_below_gap` | c² − R_anti = c²(2−4t²)/(1+t²) | proof of Thm 5.1(a) |
| `anti_above_bottom` | R_anti + c² = 6c²t²/(1+t²) | proof of Thm 5.1(a) |
| `anti_in_gap` | R_anti ∈ (−c²,c²) ⇔ 0 < t² < 1/2 | Thm 5.1(a) |
| `anti_strict_mono` | R_anti is strictly increasing in t ≥ 0 | Remark after Thm 5.1 |
| `anti_midgap` | 5(1/√5)² − 1 = 0 | mid-gap crossing, Thm 5.1(a) |

Auxiliary: `w_sq`, `w_pos`, `one_lt_w`, `rho_nonneg`.

There is no `sorry` and no added `axiom` in the file: `#print axioms`
on each of the 18 declarations returns exactly
`[propext, Classical.choice, Quot.sound]`, never `sorryAx`.

Verified on 2026-08-15 with the pinned project below:
`Build completed successfully (3079 jobs)`.

## Reproducing the check

A pinned Lake project ships alongside the source, so no `lake new` step
is needed:

```
# install elan (Lean toolchain manager), then, in this folder:
lake exe cache get          # prebuilt Mathlib oleans (several GB)
lake build                  # checks FiberLemmas.lean
```

Pins:

- `lean-toolchain` → `leanprover/lean4:v4.33.0`
- `lakefile.toml` → Mathlib tag `v4.33.0`,
  commit `db584cd6d46c92f209a44c0f1c829460d327499d`
- `lake-manifest.json` → the full resolved dependency graph
