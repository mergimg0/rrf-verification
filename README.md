# Lean 4 Verification of Weighted Reciprocal Rank Fusion

Machine-verified proofs of formal properties of the 4-component weighted Reciprocal Rank Fusion (RRF) scoring function for multi-modal, multi-scope retrieval.

## Verified Properties

| Property | Theorem | Description |
|----------|---------|-------------|
| Non-negativity | `rrf_nonneg` | Score is non-negative for all valid inputs |
| Upper boundedness | `rrf_upper_bound` | Score is bounded above by the sum of weights divided by (k+1) |
| Strict monotonicity | `rrf_full_monotone_psem` | Improving rank in any component strictly increases the score |
| Convexity | `rrf_kernel_convex` | Diminishing returns: top-rank improvements matter more |
| Scale invariance | `rrf_full_scale_invariance` | Score depends only on ordinal ranks, not cardinal scores |

16 theorem statements total, covering helper lemmas and intermediate results.

## Building

Requires [Lean 4](https://lean-lang.org/) version 4.28.0 or later.

```bash
lake build
```

The entire formalisation is self-contained (no Mathlib dependency) and builds in under 5 seconds.

## Design

All fraction comparisons are expressed via **cross-multiplication** over natural numbers, avoiding the need for real-number arithmetic or rational number theory. For example, the inequality α/(k+r₁) > α/(k+r₂) is encoded as α·(k+r₂) > α·(k+r₁).

Key types enforce domain constraints at the type level:
- `Rank`: positive natural number (val ≥ 1)
- `SmoothK`: positive smoothing constant (val ≥ 1)
- `Weight`: non-negative weight (Nat by construction)
- `RRFWeights`: the 4-component weight vector α
- `RRFRanks`: the 4-component rank vector r

## Paper

This code accompanies the paper:

> Mergim Gashi. *The Canonical Decomposition of Reciprocal Rank Fusion: Formal Derivation, Properties, and Machine-Verified Proofs for Multi-Modal Multi-Scope Retrieval.* 2026.

## License

MIT
