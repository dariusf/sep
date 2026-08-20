
# Sep

An [SLF](https://softwarefoundations.cis.upenn.edu/slf-current/index.html)-style first-order separation logic mechanisation and useful tactics for working with it, including an xsimpl-style entailment checker.

```sh
lake exe cache get
lake build
```

## What's in the box

The separation logic contains various extensions: top/and/or/sat, septraction, framing modalities ([new!](https://dariusf.github.io/thesis/)).

The xsimpl tactic supports frame inference/biabduction, and a typeclass for teaching it about new separation logics, including affine ones.
<!-- An Iris-like higher-order separation logic using it is available [here](https://github.com/dariusf/indirection). -->

Other useful, new tactics for working with separation logic are also available:
`sl_pull` and `sl_perm` allow easy reordering modulo AC.
There is also integration with Lean's `ac_nf` and `ac_rfl`, and mathlib's `grw`.
