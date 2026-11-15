# Exact divide-and-conquer recurrences

The natural-valued recurrence solver recognizes

```text
μ(f:ℕ→ℕ). λ(n:ℕ). if n<b then seed(n) else a*f(divN(n,b))+toll(n)
```

Here `b` is a literal integer at least 2. The equivalent base test `n≤b−1`
is also accepted. The coefficient is independent of `n`, and may contain
symbolic natural parameters. Multiple calls to the same subproblem, additions,
and constant multiplications are collected into one coefficient and toll.
The seed and toll must be recursion-free expressions whose totality the
simplifier can certify. Polynomial, integer-quotient, and integer-logarithm
tolls are supported; they need not be C-finite.

Examples:

```text
μ(f:ℕ→ℕ). λ(n:ℕ). if n<2 then 1 else f(divN(n,2))+1
μ(f:ℕ→ℕ). λ(n:ℕ). if n<2 then n else 2*f(divN(n,2))+n
μ(f:ℕ→ℕ). λ(n:ℕ). if n<3 then n else 3*f(divN(n,3))+n*n
```

`divN(n,b)` is exact natural-number division, rounding down, and is undefined
at `b=0`. `logN(b,n)` is the integer logarithm with the **base first**. Its
domain is `b≥2`, and `logN(b,0)=0`. Both primitives evaluate using integer
arithmetic, including for large literals. Write recursive subdivision with
`divN`; this recognizer does not translate `floorN(n/b)` automatically.

The result is an exact finite sum. With `L=logN(b,n)`, it is

```text
a^L * seed(divN(n,b^L)) + Σ(j<L) a^j * toll(divN(n,b^j))
```

This preserves the terminal subproblem for every natural input, including
zero and inputs that are not powers of `b`. The current printer can express
the natural sum through `floorN` of a real sum and retain guards inside the
summand. These expressions remain exactly evaluable. The generated Lean
certificate proves equality with the original least fixed point.

Mixed floor/ceiling subproblems, unequal split ratios, coefficients depending
on `n`, nonlinear feedback, and asymptotic bounds are not handled by this
solver. Unsupported recurrences retain their fixed-point expression.

## Verification

Build all test binaries together with `make -j2 build-tests`, then run
`./build/divide-recurrence-tests build/divide-recurrences`. This suite emits
26 Lean certificates and checks 704 exact evaluations against an independent
bottom-up recurrence evaluator, with and without proof tracing. The cases
include symbolic and zero coefficients, different split factors, rejected
partial expressions, and inputs around powers of the split factor.
