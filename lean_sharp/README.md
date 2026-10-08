# The current development — the four rungs of the document

Three independent Lean 4 + Mathlib trees. Each carries its own `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain`, so it builds on its own:

```sh
cd wC && lake exe cache get && lake build     # likewise wF, wM
```

| tree | modules | contents |
|---|---|---|
| `wC` | 54 | model (`RobustZ/Statement.lean`), carrier flatness, elementary rung, exact-criterion rung with its closed forms, the finite-`N` certificates, the coefficient-`4` closed form, and the `liminf` theorems |
| `wF` | 35 | the Jensen rung (`2π/e`) and the complexification bridge |
| `wM` | 47 | the weak-constant `8/e` variant |

| result | declaration | file |
|---|---|---|
| elementary (`4/e`), every order | `elementary_bound`, `elementary_bound_pi` | `wC/RobustZ/ElementaryBound.lean` |
| Jensen (`2π/e`), every order | `jensen_rung_final`, `jensen_rung_pi_final`, `jensen_ratio_tendsto` | `wF/RobustZ/JensenBridge.lean`, `wF/RobustZ/JensenRung.lean` |
| exact criterion, coefficient `→ 4` | `new_rung_final`, `nr_closed_form` | `wC/RobustZ/RungFinal.lean`, `wC/RobustZ/NewRung.lean` |
| certified integers at `φ = π` | `cert_N2`–`cert_N4`, `cert_N5_tight`–`cert_N12_tight` | `wC/RobustZ/RungFinal.lean`, `wC/RobustZ/RungTight.lean` |
| `8/e` variant | `eight_over_e_bound` | `wM/RobustZ/EightOverE.lean` |
| coefficient, with side conditions | `c_ge_four`, `c_ge_four_or_grows` | `wC/RobustZ/Theorem.lean` |

No `sorry`, `admit` or `axiom` occurs in the sources; the `RobustZ/Audit*.lean` files print the
axioms of the headline declarations with `#print axioms`. These names and paths are the ones the
document's Table IV refers to; the verification page is <https://show.dytchem.cn/lean/>.
