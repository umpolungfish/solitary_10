# Solitary 10

A proof that $10$ is solitary: no integer $m \neq 10$ satisfies $\sigma(m)/m = 9/5$.

## The Result

A positive integer $n$ is **solitary** if it is the unique positive integer with its abundancy index $\sigma(n)/n$. Since $\sigma(10) = 18$, we need to show that $\sigma(m)/m = 9/5$ has no solution other than $m = 10$.

## Proof Strategy

Every candidate $m$ factors as $m = 2^a \cdot 5^b \cdot r$ with $\gcd(r, 10) = 1$. The equation $5\sigma(m) = 9m$ then constrains $\sigma(r)/r$ to a specific rational depending on $(a, b)$.

Two tools close the argument:

1. **Lower bound $\sigma(r)/r \geq 1$** collapses the infinite $(a, b)$ plane to eight candidate pairs.
2. **Iterated denominator-divisibility lemma**: if $\sigma(r)/r = A/B$ in lowest terms, every prime of $B$ must divide $r$; pulling that prime out and iterating propagates the constraint into a contradiction.

Of the eight candidates, four die immediately (their denominators carry a factor of $2$ or $5$, forbidden by $\gcd(r,10)=1$), three die after one cascade step, and one survives: $(a,b) = (1,1)$, $r = 1$, giving $m = 10$.

## Files

| File | Contents |
|------|----------|
| `SOLITARY_10.md` | Full proof with commentary |
| `SOLITARY_10.tex` | LaTeX source |
| `SOLITARY_10.pdf` | Compiled PDF |

---

*Structural type: $\langle D_\infty; T_\bowtie; R_\leftrightarrow; P_\pm; F_\hbar; K_\text{slow}; G_\aleph; \Gamma_\text{seq}; \Phi_c; H_2; n{:}m; \Omega_{\mathbb{Z}_2} \rangle$*
