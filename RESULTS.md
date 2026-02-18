# Implementation Report: Weighted RRF Formal Verification in Lean4
Generated: 2026-02-17

## Task
Formally verify five properties of the weighted Reciprocal Rank Fusion (RRF)
scoring function in Lean4. The 4-component weighted RRF is:

```
score(q, z_i) = alpha_psem * 1/(k + rank_psem)
              + alpha_plex * 1/(k + rank_plex)
              + alpha_xsem * 1/(k + rank_xsem)
              + alpha_xlex * 1/(k + rank_xlex)
```

## Build Status

**CLEAN BUILD: Zero errors, zero warnings, zero incomplete proofs.**

```
$ lake build
Build completed successfully (3 jobs).
```

- Lean version: 4.28.0
- No Mathlib dependency (pure core Lean4)
- All proofs are constructive with no axiom usage beyond Lean4 core

## Approach

Since Mathlib download was prohibitively slow (~8000 cached files), all proofs
use only core Lean4 tactics: `omega`, `simp`, `rfl`, `apply`, `exact`, `rw`,
`unfold`, `have`, `let`, `show`, `calc`, `intro`, `constructor`.

To avoid real-number division in Lean4 (which lacks a built-in `Real` type),
all fraction comparisons are expressed via **cross-multiplication** over `Nat`.
For example, `alpha/(k+r1) > alpha/(k+r2)` is proven as `alpha*(k+r2) > alpha*(k+r1)`.

Key challenge: Lean4's `omega` tactic handles only **linear** arithmetic.
All nonlinear products (e.g., `(k+r+1)*(k+r+2)`) required manual decomposition
using `Nat.left_distrib`, `Nat.add_mul`, `Nat.mul_comm` before `omega` could
close the linear residuals.

## Proven Properties

### 1. Non-negativity (`rrf_nonneg`)
**Statement:** The RRF score is non-negative when all weights >= 0 and k > 0.

**Proof strategy:** Weights are modeled as `Nat` (non-negative by construction).
The RRF numerator (with positive common denominator) is a sum of products of
`Nat` values, hence itself a `Nat`, hence >= 0. Proof is `Nat.zero_le _`.

### 2. Upper Boundedness (`rrf_upper_bound`)
**Statement:** score <= (sum alpha_i) / (k + 1)

**Proof strategy:** Since rank >= 1, each denominator (k + rank) >= (k + 1),
so each component alpha_i/(k+rank_i) <= alpha_i/(k+1). The cross-multiplied
form is: `(sum alpha_i) * (k+1) <= sum (alpha_i * (k + rank_i))`. Proven by
distributing the LHS via `Nat.add_mul` and applying `Nat.add_le_add` to the
four per-component bounds from `single_component_upper_bound`.

### 3. Monotonicity (`rrfDenom_strict_mono`, `rrf_component_monotone`, `rrf_score_improvement`, `rrf_full_monotone_psem`)
**Statement:** If rank1 < rank2, then 1/(k+rank1) > 1/(k+rank2). Better ranks
in any component lead to higher overall scores.

**Proof strategy:** The denominator `rrfDenom k r = k + r` is strictly increasing
in `r` (trivial by `omega`). For weighted components, `alpha*(k+r2) > alpha*(k+r1)`
when `r1 < r2` and `alpha > 0`, proven via `Nat.mul_lt_mul_of_pos_left`.

### 4. Convexity / Diminishing Returns (`rrf_kernel_convex`, `diminishing_returns`, `rrf_kernel_jensen`)
**Statement:** The RRF kernel f(r) = 1/(k+r) is convex: f''(r) > 0. In discrete
form: the marginal gain from improving rank r+1 to r exceeds the gain from r+2 to r+1.

**Proof strategy (convexity):**
Cross-multiplied: `(k+r+1)*(k+r+2) > (k+r)*(k+r+1)`. Let m = k+r. Then
`(m+1)*(m+2) = (m+1)*m + (m+1)*2` and `m*(m+1) = (m+1)*m`, so the difference
is `2*(m+1) > 0`. Products decomposed via `Nat.left_distrib` and `Nat.mul_comm`.

**Proof strategy (Jensen):**
`(k+r)*(k+r+2) < (k+r+1)^2`. Let m = k+r. Then `m*(m+2) = m^2 + 2m` and
`(m+1)^2 = m^2 + 2m + 1`, difference is 1. Products decomposed manually.

### 5. Scale Invariance (`rrf_full_scale_invariance`, `monotone_preserves_ordering`)
**Statement:** The RRF score depends only on ordinal ranks. Any monotone
transformation of underlying similarity/BM25 scores preserves the RRF score.

**Proof strategy:** Two parts:
- `monotone_preserves_ordering`: A strictly monotone function `f` applied to
  scores preserves the ordering relation, hence preserves ranks.
- `rrf_full_scale_invariance`: The RRF numerator and common denominator are
  pure functions of (weights, k, ranks). If two rank vectors are component-wise
  equal, the scores are identical. Proven by `unfold` + `rw`.

## Theorem Index

| Theorem | Property | Line |
|---------|----------|------|
| `rrf_nonneg` | Non-negativity | 92 |
| `single_component_upper_bound` | Upper bound (per component) | 111 |
| `rrf_upper_bound` | Upper bound (full score) | 120 |
| `rrfDenom_strict_mono` | Monotonicity (denominator) | 155 |
| `rrf_kernel_decreasing` | Monotonicity (kernel, raw Nat) | 162 |
| `rrf_component_monotone` | Monotonicity (weighted component) | 169 |
| `rrf_score_improvement` | Monotonicity (score improvement) | 179 |
| `rrf_full_monotone_psem` | Monotonicity (full 4-component) | 192 |
| `rrf_kernel_convex` | Convexity (discrete) | 234 |
| `diminishing_returns` | Convexity (diminishing returns) | 251 |
| `rrf_kernel_jensen` | Convexity (Jensen's inequality) | 264 |
| `monotone_preserves_ordering` | Scale invariance (ordering) | 303 |
| `rrf_scale_invariance_numerator` | Scale invariance (numerator) | 319 |
| `rrf_scale_invariance_denom` | Scale invariance (denominator) | 331 |
| `rrf_full_scale_invariance` | Scale invariance (full) | 343 |
| `rrfCommonDenom_pos` | Bonus: denominator positivity | 359 |

## Files

| File | Purpose |
|------|---------|
| `/Users/mghome/proofs/rrf_verification/RrfVerification.lean` | All definitions and proofs (398 lines) |
| `/Users/mghome/proofs/rrf_verification/lakefile.toml` | Lake project config (no Mathlib) |
| `/Users/mghome/proofs/rrf_verification/lean-toolchain` | Lean 4.28.0 |

## Design Decisions

1. **No Mathlib:** Mathlib cache download (~8000 files) was too slow. All proofs
   use only core Lean4 tactics, making the project self-contained and fast to build.

2. **Nat encoding:** Weights, ranks, and k are all `Nat`. This makes non-negativity
   trivial by construction. Fraction comparisons use cross-multiplication.

3. **Manual nonlinear decomposition:** Lean4's `omega` handles only linear
   arithmetic. All quadratic terms required manual factoring via `Nat.left_distrib`,
   `Nat.add_mul`, and `Nat.mul_comm` before `omega` could close the goal.

4. **Structured types:** `Rank`, `SmoothK`, `Weight`, `RRFWeights`, `RRFRanks`
   encode domain constraints (rank >= 1, k >= 1) as structure invariants, making
   invalid states unrepresentable.
