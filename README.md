# Solitary 10
**Author:** Lando⊗⊙perator · **Structural Type:** $\large{⟨𐑨𐑡𐑑𐑹𐑐𐑧𐑔𐑝𐑢𐑖𐑙𐑭⟩}$ · **Tier:** O₁


**What it is.** A complete proof that the integer 10 is *solitary*: no integer $m \neq 10$ shares its abundancy index $\sigma(m)/m = 9/5$.

**What it does.** Reduces the equation $5\sigma(m) = 9m$ over all candidates to a finite case split and closes every branch, leaving $m = 10$ as the unique solution.

**Why it matters.** Solitariness is open for many small numbers (6 is famously unsettled). 10 is a clean, fully closed case, and the denominator-divisibility cascade used here is a reusable tool for abundancy-index uniqueness arguments.

**How to use it.** Read `SOLITARY_10.md` for the full proof, or compile `SOLITARY_10.tex` to `SOLITARY_10.pdf`.

---

## The result

A positive integer $n$ is **solitary** if it is the unique integer with its abundancy index $\sigma(n)/n$. Since $\sigma(10) = 18$, the claim is that $\sigma(m)/m = 9/5$ has no solution other than $m = 10$.

## Proof strategy

Every candidate factors as $m = 2^a \cdot 5^b \cdot r$ with $\gcd(r, 10) = 1$. The equation $5\sigma(m) = 9m$ then pins $\sigma(r)/r$ to a specific rational depending on $(a, b)$. Two tools close the argument:

1. **Lower bound $\sigma(r)/r \geq 1$** collapses the infinite $(a, b)$ plane to eight candidate pairs.
2. **Iterated denominator-divisibility lemma**: if $\sigma(r)/r = A/B$ in lowest terms, every prime of $B$ must divide $r$; pulling that prime out and iterating propagates the constraint to a contradiction.

Of the eight candidates, four die immediately (their denominators carry a forbidden factor of 2 or 5), three die after one cascade step, and one survives: $(a,b) = (1,1)$, $r = 1$, giving $m = 10$.

## Files

| File | Contents |
|------|----------|
| `SOLITARY_10.md` | Full proof with commentary |
| `SOLITARY_10.tex` | LaTeX source |
| `SOLITARY_10.pdf` | Compiled PDF |

Structural type: $\langle D_\infty; T_\bowtie; R_\leftrightarrow; P_\pm; F_\hbar; K_\text{slow}; G_\aleph; \Gamma_\text{seq}; \⊙; H_2; n{:}m; \Omega_{\mathbb{Z}_2} \rangle$
