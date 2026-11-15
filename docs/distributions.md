# Non-recursive distributions and continuity capabilities

This is an initial, intensional **presentation** semantics. It retains pointwise
weights and unevaluated integral requests; it does not quotient by equality of
measures. It is not yet a complete algebra of distributions. In particular,
commutative-monad, change-of-variables, and Fubini laws are not assumed. Adding a
law requires proving it for the supported observers, including pointwise density
extraction. Observational equality of presentations is not exposed as source
equality.

## Types and syntax

`Distribution(A)` (also `Dist(A)`) is a type constructor. Its argument may be any
currently supported binding type, including functions, sets, type codes, and
distributions. This provides distributions over existing type codes; it does not
extend the existing type-code universe or dependent subtype support.

```text
δ(2)                               # Distribution(ℕ), following literal inference
(δ(2):Distribution(ℝ))              # Explicitly real-valued
δ(λ(n:ℕ).n)                        # Distribution(ℕ→ℕ)
δ(Distribution(ℝ))                 # Distribution(Type)
δ(δ(2))                            # Distribution(Distribution(ℕ))
Λ(x:ℝ). [x≠0]·λ[x]                # Retains the puncture
Λ(x:ℝ). δ(0)[x]+[x≠0]·λ[x]       # Mixed discrete/continuous presentation
∫(x:ℝ). x·δ(2)[x]                 # Finite scalar integral request
([x≠0]·λ[x])//λ[x]                 # Supported pointwise density extraction
Λ(x:ℝ). ∫(y:ℝ). δ(y)[x]·λ[y]      # Distribution-valued marginalization request
```

`Λx. ...` and `∫dx ...` default the bound type to `ℝ`. Use annotated binders for
other types. `distribution(x:A). ...` and `integral(x:A). ...` are ASCII binder
aliases; `dirac(v)` is the ASCII spelling of `δ(v)`.

`d[x]` is an output form, not an ordinary function application or a scalar
density. In this first elaborator, each output form has exactly one distribution
factor for its axis. Scalar factors become pointwise weight functions; sums
become sums of presentations. `δ(v)[x]` requires `v` to be independent of the
output variable `x`. Products of distributions for the same axis are rejected.
Nested marginalization currently requires one explicit integration factor
`d[y]`, independent of the outer output axis; arbitrary joint forms are not yet
supported.

The canonical printer uses the equivalent constructor syntax:

| Constructor | Meaning |
| --- | --- |
| `dirac(v)` | Point atom at a defined value |
| `zeroD(A)` | Zero presentation over `A` |
| `lebesgueD()` | Real Lebesgue presentation |
| `addD(p,q)` | Sum |
| `scaleD(r,p)` | Real scalar weight, including negative weights |
| `weightD(f,p)` | Pointwise weighting by `f : A→ℝ` |
| `bindD(p,k)` | Explicit composition with a distribution-valued function |
| `integralD(k)` | Real-indexed, distribution-valued integral request |
| `massD(p)` | Strict finite scalar integral of the constant one |
| `densityAtD(p,x)` | Supported pointwise real density at `x` |

Singular atoms have no supported Lebesgue density rule. Their density extraction
returns `none`, not zero. Mixtures containing such an atom therefore also have no
supported density extraction. This initial operation is deliberately narrower
than general symbolic disintegration.

## Mathematical interpretation and proof boundary

`QSym.Distribution.Presentation` is a universe-preserving inductive type with
point atoms, continuous-source presentations, sums, scaling, and real integral
requests. An internal invalid-request node preserves failure inside integral
branches. Function-valued fields retain their pointwise values and undefinedness.
Forming a presentation requires no sigma-algebra on its result type.

The finite scalar observer uses `partialIntegral`: every integrand point must be
defined, and the real-valued integrand must be Bochner integrable. Failure is
`none`; the totalized zero value of a nonintegrable Mathlib integral is never
exposed as a valid answer. Nested requests check the same conditions recursively.
Different integration orders can have different domains, so reordering is not a
permitted rewrite without further hypotheses.

The frontend reduces Dirac scalar integrals and pointwise extraction from a
weighted Lebesgue presentation using proved equalities. Other requests remain
symbolic. Generated Lean
certificates check reductions against the presentation semantics. Native source
elaboration is not itself a proof: a generated certificate must pass the kernel
before its result is trusted. No new axioms or `sorry`s are introduced.

## Continuity is relative to an input

Here continuity means preservation of increasing chains in the approximation
order. Current scalar recursion uses flat partial information, so its continuity
requirements differ from continuity in the usual numerical order on reals.

`Bindings.continuity(term, recursiveIndex)` infers one of three capabilities:

* `constant`: no dependency on that recursion variable;
* `continuous`: dependency passes only through supported continuous constructs;
* `unsupported`: a dependency crosses an operation with no supported proof.

The first rule applies to *every* operation, including strict integrals. Thus an
integral may depend on the ordinary argument `n`, or on captured data, and still
be constant in the recursive function `f`. The checker does not ban every fixed
point containing an integral. Strict distribution primitives can also consume continuously produced atomic
values: `massD(δ(f(n)))` is admitted. Its intermediate presentation is ordered by
flat partial information, so strict lifting proves continuity. By contrast,
`massD(Λ(x:ℝ). f(n)·λ[x])` is rejected: the weight function closes over the
recursive variable, and treating that function as a flat atomic value would be
incorrect. A kernel capability with pointwise order is required there. User assertions
do not grant continuity. Existing recursive certificates independently construct
the continuous `Recursion.Program` interpretation in Lean.

This is an inferred capability judgment, not yet a new surface arrow type. Its
soundness is scoped to the existing first-order recursion grammar. Higher-order
capabilities, latent argument dependencies, and annotations backed by generated
proofs remain subsequent extensions.

## Undefined contributions as zero

`QSym.PositiveIntegral` supplies a separate positive integration interface:

* `zeroExtendHom : Part ℝ≥0∞ →𝒄 ℝ≥0∞` sends an undefined contribution to zero;
* `integralHom` integrates pointwise continuous nonnegative integrands;
* `partialIntegralHom` composes those constructions.

The integral hypotheses require almost-everywhere measurability at each parameter
and pointwise continuity in the approximation parameter. Monotone convergence
then proves continuity of the integral, with no finite-total-mass requirement.
The codomain is ordered `ℝ≥0∞`, allowing increasing mass and infinity.
This is a continuity theorem; joint measurability of random kernel parameters
remains a separate obligation for a higher-order probabilistic interpretation.

This operation does not change pointwise density extraction or strict finite
integration. It is not appropriate for silently discarding invalid arithmetic;
if errors should propagate, the semantic domain must distinguish them from an
undefined contribution. Signed values cannot use this monotonicity argument.
The positive interface is currently Lean-only; no source positive-integral
primitive is admitted to recursion until its elaboration produces these proofs.

## Next extensions

1. Add source types for ordered nonnegative mass and proof-bearing measurable,
   continuous kernels; emit `partialIntegralHom` certificates compositionally.
2. Add support-sensitive rules: finite-support integration, dead branches,
   certified zero weights, and dependence removed by proven simplification.
3. Prove selected algebra and disintegration rules against all supported
   observers, with integrability, measurability, and coordinate hypotheses.
4. Extend recursive result domains and higher-order capability signatures only
   after defining their approximation orders.
