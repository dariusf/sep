
# Sep

An [SLF](https://softwarefoundations.cis.upenn.edu/slf-current/index.html)-style first-order separation logic mechanisation and useful tactics for working with it, including an xsimpl-style entailment checker.

```sh
lake exe cache get
lake build
```

## What's in the box

The separation logic contains various extensions: top/and/or/sat, septraction, framing modalities ([new!](https://dariusf.github.io/thesis/)).

The xsimpl tactic supports frame inference and biabduction. It can be used with other separation logics (including affine ones) by providing a typeclass instance.
<!-- An Iris-like higher-order separation logic using it is available [here](https://github.com/dariusf/indirection). -->

Other useful, new tactics for working with separation logic are also available:
`sl_pull` and `sl_perm` allow easy reordering modulo AC.
There is also integration with Lean's `ac_nf` and `ac_rfl`, and mathlib's `grw`.

There is an experimental tactic, xsearch, which heuristically handles various kinds of inductive predicates (unlike xsimpl, which is deliberately simple and predictable, and works only on "straight-line" entailments) and is competitive on the SL-COMP 2019 benchmarks[^1].

[^1]: xsearch produces correct answers for all 983 problems in the six entailment divisions (including 9 mislabelled ones). It is also quite fast (~2.8x faster than the strongest solver S2S, though this is not a fair comparison due to differences in e.g. hardware).
