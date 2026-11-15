# Summation reference audit

Reference: [tgehr/sym, lebesgue/summation.d](https://github.com/tgehr/sym/blob/lebesgue/summation.d), retrieved 2026-11-15.
SHA-256 of the inspected source: `01fc8e2fff3d454cf2662c58b05daa9be1801b6fdbb4e96a244b33a789ffae3f`.
The branch URL is mutable; this hash identifies the version compared.

This is an incremental parity improvement, not a claim of complete parity.

## Comparison

| Reference operation | qsym coverage and remaining differences |
| --- | --- |
| Factor index-independent terms; sum polynomial/geometric terms | Checked antidifference candidates already cover polynomial-geometric combinations with numeric ratios. Finite weighted sums also handle symbolic ratios, with a separately verified ratio-1 branch. This patch retries otherwise unrecognized summands after normalization, while checking candidates against the original summand. The original form is tried first so that zero-base powers remain recognizable. |
| Polynomial power sums | A separate exact sparse-polynomial path handles higher powers and polynomial parameter coefficients without the old fixed degree-32 cutoff. It uses coefficient arithmetic for native verification and independent Lean ring proofs for the original typed identities. |
| Signed affine geometric exponents | Nonzero bases now split arbitrary integer exponent offsets and literal integer multiples. This covers symbolic rounded lower endpoints and shifted/scaled geometric tails in rational, real, and complex arithmetic. Zero-base domain restrictions remain checked. |
| Finite intervals with rounded real bounds | Both bounds are combined before reindexing. Positive integer affine index expressions and integer shifts are moved to the bounds. Strict and inclusive endpoints use the existing certified rounding rules. |
| Equality selectors and excluded points | Real and rational selectors become rounded intervals; noninteger selectors contribute zero. Real exclusions split into two strict intervals. Multiple integer exclusions are processed recursively. |
| Distribute a product containing a masked addition | Distribution is exposed when it enables a finite or provably convergent part to be solved. Casts are moved through masks where the existing exact embedding lemmas apply. |
| Retain an opaque remainder after summing other terms | A new exact partial-value linearity theorem permits splitting if either side is proved defined as an absolutely convergent sum. Both divergent sides are never split on this basis. |
| General discrete antiderivative by summation by parts | A bounded recursive Abel search now supplements coefficient matching for finite sums. It memoizes unknown primitives, recursively integrates the residual, and solves affine cycles. Fractional affine real powers with positive numeric bases are covered when the existing identity/domain checker can certify the result. Unrestricted real/symbolic affine exponents remain a gap. |
| Arbitrary numeric finite-range enumeration | qsym retains its 64-term unfolding limit; the reference has no explicit limit. Larger supported sums use antidifferences. Larger opaque sums remain symbolic. |
| Infinite endpoint limits | qsym requires checked absolute convergence and a sum in the result type. The reference's general limit-based approach is not implemented. |
| `DDeltaOld` / `DDistApply` substitutions and fact propagation | These legacy distribution operations have no direct equivalent in this scalar summation implementation. They are not covered by the scalar parity work. |

Remaining examples include `∑(i:ℕ). i·q^i` for symbolic `q`, and `∑(i:ℕ). [i<n]·q^(a·i+b)` for general real `a,b,q`.
Negative, fractional, and symbolic affine bound coefficients also need additional handling.
No convergence or nonzero assumption is invented to produce a result for these cases.

## Polynomial degree and verification cost

The former path could find an antiderivative for `i^6` or `i^10`, then exhaust
the general rewrite budget while verifying its successor identity. Retrying
Abel search made this failure more expensive. Polynomial sums of degree four
and above now use exact sparse coefficient arithmetic, including symbolic
polynomial coefficients and natural/integer/rational/real/complex embeddings.
Binomial expansion of successor expressions uses a direct recurrence instead
of repeatedly multiplying growing coefficient tables.

The zero and successor checks are replayed by Lean against the original typed
expression using `norm_num`, cast normalization, and `ring_nf`. Native
coefficient tables are not trusted proof evidence. The polynomial recognizer
excludes partial natural subtraction, symbolic reciprocals, and other
non-polynomial operations; it cannot erase their domains by cancellation.
Its resource limits bound arithmetic work, expanded terms, and coefficient
size, rather than imposing a fixed maximum polynomial degree.

The exact reported examples now reduce to closed forms, retaining the natural
result type and its rounding wrapper. Regressions cover degrees through 100,
shifted polynomials, symbolic coefficients, rational and complex values, and
integer intervals. General infinite limits, including symbolic geometric convergence conditions,
remain separate gaps.

## Symbolic weighted finite sums

The polynomial-geometric candidate solver now checks its zero and successor
identities using exact rational functions and affine natural exponents. Each
algebraic mask is checked in both branches; inverse operands must be proved
nonzero in the active branch. The native computation is untrusted: Lean
replays the original typed expressions with case splits and field/ring proofs.
This covers `i*q^i`, `i^k*q^i`, polynomial parameter coefficients, multiple
ratios, real/rational/complex ratios, and shifted/scaled natural exponents.
The removable ratio-1 branch is retained, including `q=-1` when the actual
ratio is `q^2`. No nonzero or convergence assumption is silently inserted.

The scalar normalizer skips speculative zero searches under guards containing
only disequalities. Equality, disjunction-of-equalities, and order assumptions
retain the existing zero search.
Polynomial primitives keep rational coefficients in rational arithmetic until
the final embedding, reducing repeated embedding contraction. Applied lambdas
are normalized after substitution, and strict total scalar endpoints (including `floorN(ceil(n))`) instantiate a
sum primitive directly. These are checked equalities, including endpoint domains.

The existing degree-32/component limits still apply to polynomial-geometric
candidate generation. The separate polynomial-only path has no fixed degree
cutoff. General real/symbolic affine exponents and symbolic infinite-tail
convergence remain gaps; this is not a claim of full reference parity.

## Recursive Abel search

For a polynomial factor `P` and a candidate primitive `G` of the remaining
factor, the fallback constructs `P*G - antidifference((P(n+1)-P(n))*G(n+1))`.
This uses the same discrete integration-by-parts identity as the reference.
Active memo entries hold fresh scalar placeholders. An affine self-reference
`F = A*F+B` closes as `B/(1-A)`; solved placeholders are substituted into
dependent entries. For example, integrating `n` produces
`F=n^2-F-n`, hence `F=(n^2-n)/2`.

The memo table is local to one invocation. The search rejects nonlinear cycles,
singular divisors, index-dependent cycle coefficients, and attempts to shift an
unresolved scalar placeholder. It checks that no placeholders remain in the
returned expression. Limits are 384 recursive calls, depth 64, polynomial
factor degree 32, and bounded simplification of each intermediate expression.
Failure leaves the summation symbolic. This is a bounded implementation of the
reference's recursive mechanism, not unrestricted symbolic integration.

Coefficient matching remains the fast path. Abel is attempted when that path
cannot produce a candidate or its candidate fails certification. Both paths
must establish the zero value and successor identity against the original
summand, including definedness. Infinite sums retain the existing checked
polynomial-geometric tail/convergence path; Abel candidates do not bypass it.

Additional opt-in scalar equations expand exponential sums and positive-base
real powers of a sum. Real-power expansion requires a positivity proof; the
normalizer currently supplies it only for positive numeric bases. Exponential
candidates whose identities cannot be certified still remain symbolic.

For example, the finite sums of `i*2^(i/2)` and `i^2*4^(i/2)` now have checked
closed forms even with a symbolic natural upper bound.

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
155 independent exact numeric checks, one unsupported infinite symbolic-ratio case, and an unsupported nonlinear bound.
It is included in `make test` and its 25 certificates in `tools/verify.py`.

`build/summation-abel-tests build/summation-abel` exercises the recursive search
directly (including rational and complex embeddings, memo hits, and cycle
closure), six new finite-sum families, explicit prefix evaluations, and rejected
partial or unsupported candidates. Its 22 certificates are included in
`tools/verify.py`.

`build/polynomial-summation-tests build/polynomial-summation` checks 107 exact
prefix values, reports per-case solver timings, rejects invalid polynomial
identities, and checks recovery after budget exhaustion. Its 14 certificates
are included in `tools/verify.py`.

`build/weighted-summation-tests build/weighted-summation` checks 560 exact
values against independent finite sums, including traced and untraced results,
zero/unit/negative/rational/complex ratios, and affine natural exponents. It
also rejects five invalid rational identities and retains four guarded-zero
regressions. Its 16 certificates are included in `tools/verify.py`.

The rational proof exporter uses a common inverse power before clearing
denominators, avoiding repeated multiplication of equal denominators. Its
supporting algebraic lemmas are checked by Lean's kernel along with each
certificate; the native coefficient computation is never trusted.

The new binder rules use exact `Binding.Reduction` equalities. Candidate search is
untrusted; finite zero/successor identities, domains, and infinite tail convergence
are still certified before a candidate is used. An exhausted candidate search
leaves the sum symbolic rather than asserting an identity.

### Performance and verification of this follow-up

Compared with the previous polynomial patch, using LDC 1.42.0 with the same
unoptimized `-boundscheck=on` shared test engine:

| `∑(i:ℕ). [i<n]·i^10` | Previous patch | This patch |
| --- | ---: | ---: |
| Declared `n:ℕ` | 35.8 ms | 13.8 ms |
| Undeclared `n` (real, rounded endpoint) | 287.3 ms | 52.3 ms |

These are medians of three alternating runs, each averaging five consecutive
evaluations in one session. They include parsing and simplification; they are
not a direct timing comparison with `sym`. The tests also retain per-case
solver timings for reproducibility on other machines.

All 93 native test suites passed. Lean checked the 30 polynomial/weighted-sum
certificates plus 12 representative existing summation, conditional-application,
and partial-domain certificates. This is targeted kernel verification, not a
claim that the entire `make verify` certificate collection was rerun.
