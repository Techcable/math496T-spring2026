# Key Theorems
Super important Lean theorems that I don't want to forget.

## Analysis

### Properties of Reals
- `le_antisymm` - Squeeze lemma - $x \le y \land y \le x \implies x = y$
- `le_of_forall_pos_lt_add` - The "epsilon principle" - $\forall \epsilon > 0, 0 \le x < \epsilon \implies x \le 0$.
    This is what Tonatiuh called this. Apparently it originates from Pugh's Real Analysis.
- `exists_nat_one_div_lt` - `\forall n : \N, x < 1/n \implies \forall \epsilon>0, x \le 1/n`
- `exists_rat_btwn` - Density of rationals in the reals

### Properties of `inf/sup`
- `csSup_le`, `le_csSup` and friends - Much nicer than expanding the definition, which requires an awkward `Classical.choose`

