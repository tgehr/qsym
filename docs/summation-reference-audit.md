# Summation reference audit

Reference: [tgehr/sym, lebesgue/summation.d](https://github.com/tgehr/sym/blob/lebesgue/summation.d), retrieved 2026-11-15.
SHA-256 of the inspected source: `01fc8e2fff3d454cf2662c58b05daa9be1801b6fdbb4e96a244b33a789ffae3f`.
The branch URL is mutable; this hash identifies the version compared.

This is an incremental parity improvement, not a claim of complete parity.

## Comparison

| Reference operation | qsym coverage and remaining differences |
| --- | --- |
| Factor index-independent terms; sum polynomial/geometric terms | Checked antidifference candidates already cover polynomial-geometric combinations with numeric ratios. This patch retries otherwise unrecognized summands after normalization, while checking candidates against the original summand. The original form is tried first so that zero-base powers remain recognizable. |
| Signed affine geometric exponents | Nonzero bases now split arbitrary integer exponent offsets and literal integer multiples. This covers symbolic rounded lower endpoints and shifted/scaled geometric tails in rational, real, and complex arithmetic. Zero-base domain restrictions remain checked. |
| Finite intervals with rounded real bounds | Both bounds are combined before reindexing. Positive integer affine index expressions and integer shifts are moved to the bounds. Strict and inclusive endpoints use the existing certified rounding rules. |
| Equality selectors and excluded points | Real and rational selectors become rounded intervals; noninteger selectors contribute zero. Real exclusions split into two strict intervals. Multiple integer exclusions are processed recursively. |
| Distribute a product containing a masked addition | Distribution is exposed when it enables a finite or provably convergent part to be solved. Casts are moved through masks where the existing exact embedding lemmas apply. |
| Retain an opaque remainder after summing other terms | A new exact partial-value linearity theorem permits splitting if either side is proved defined as an absolutely convergent sum. Both divergent sides are never split on this basis. |
| General discrete antiderivative by summation by parts | The existing polynomial-geometric candidate search is still narrower. Symbolic weighted geometric ratios and general real/symbolic affine exponents remain gaps. Their unsuccessful candidate checks now have explicit work limits. |
| Arbitrary numeric finite-range enumeration | qsym retains its 64-term unfolding limit; the reference has no explicit limit. Larger supported sums use antidifferences. Larger opaque sums remain symbolic. |
| Infinite endpoint limits | qsym requires checked absolute convergence and a sum in the result type. The reference's general limit-based approach is not implemented. |
| `DDeltaOld` / `DDistApply` substitutions and fact propagation | These legacy distribution operations have no direct equivalent in this scalar summation implementation. They are not covered by the scalar parity work. |

Remaining examples include `∑(i:ℕ). [i<n]·i·q^i` for symbolic `q`,
`∑(i:ℕ). i·q^i`, and `∑(i:ℕ). [i<n]·q^(a·i+b)` for general real `a,b,q`.
Negative, fractional, and symbolic affine bound coefficients also need additional handling.
No convergence or nonzero assumption is invented to produce a result for these cases.

## Representative results

```
∑(i:ℤ). [-3≤i]·(1/2)^(3·i+2)                     = 1024/7
∑(i:ℤ). [-3≤i]·(i+2)·(1/2)^(2·i+1)               = -256/9
∑(i:ℤ). [a≤i]·(1/2)^i                            = 2·(1/2)^ceil(a)
∑(i:ℤ). [-3≤i]·[i≠2]·[i≠4]·i/2^i                 = -131/4
∑(i:ℤ). ([0≤i]·[i≤2]+[4≤i]·[i≤5])·i              = 12
∑(i:ℕ). ([i<4]·i+[4≤i]·i^2)·(1/2)^i              = 19/4
```

For example, `∑(i:ℤ). [0≤i]·(1/2)^i+[0≤i]·f(i)` now produces
`2` plus the reindexed unresolved sum of `f`. The certificate establishes equality
including definedness; it does not assume that `f` is summable.

## Verification

`make -j2 build-tests` builds the shared engine once per test mode and all test
executables together. `build/summation-parity-tests build/summation-parity` covers
17 exact cases, five symbolic families, three partial-linearity certificates,
155 independent exact numeric checks, two unsupported symbolic-ratio cases, and an unsupported nonlinear bound.
It is included in `make test` and its 25 certificates in `tools/verify.py`.

The new binder rules use exact `Binding.Reduction` equalities. Candidate search is
untrusted; finite zero/successor identities, domains, and infinite tail convergence
are still certified before a candidate is used. An exhausted candidate search
leaves the sum symbolic rather than asserting an identity.
