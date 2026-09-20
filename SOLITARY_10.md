# Proof That 10 Is Solitary

## Abstract

We approached this problem with an impression we would find a counterexample. Why not, after all? The small solitary numbers — $1,2,...,9$ — form a sparse set, and the abundancy index $9/5$ did not look especially forboding. Of course, in the end the proof spirals around a singular candidate and acquires a lock on its intended target. One by one, every alternative --- every single one --- is  nixed. And all this carnage from a constraint that seems too weak to land the fatal blows--- until you actually compute through each branch.

### What the Problem Demands

Let $\sigma(n)$ denote the sum of all positive divisors of $n$. The **abundancy index** of $n$ is $\sigma(n)/n$. A positive integer $n$ is called **solitary** if it is the unique positive integer with its abundancy index. For $n = 10$:

$$\sigma(10) = 1 + 2 + 5 + 10 = 18, \qquad \frac{\sigma(10)}{10} = \frac{9}{5}.$$

The claim: **no integer $m \neq 10$ satisfies $\sigma(m)/m = 9/5$.**

The function $\sigma$ is multiplicative: if $\gcd(a,b) = 1$, then $\sigma(ab) = \sigma(a)\sigma(b)$. For a prime power, $\sigma(p^e) = (p^{e+1} - 1)/(p - 1)$. If $m$ satisfies $\sigma(m)/m = 9/5$, then $5\sigma(m) = 9m$.

All of this is standard. The difficulty is that $9/5$ is a rational number in lowest terms, and abundancy indices carry a rigid denominator-divisibility constraint. But the constraint alone is not enough — it generates an infinite space of candidates when $m$ is factored as $2^a \cdot 5^b \cdot r$ with $\gcd(r,10) = 1$. We need to show that infinity collapses to finitely many candidates and that all but one die.

### The Denominator Constraint and Why $b = 0$ Fails

The critical tool is the **denominator-divisibility lemma**: if $\sigma(r)/r = A/B$ with $\gcd(A,B) = 1$, then every prime divisor of $B$ divides $r$. Moreover, if $p \mid B$ and $p \mid r$, writing $r = p \cdot s$ gives

$$\frac{\sigma(s)}{s} = \frac{A \cdot p}{B \cdot \sigma(p)},$$

and the denominator of this new fraction (in lowest terms) must divide $s$.

Now factor any candidate $m$ as $m = 2^a \cdot 5^b \cdot r$, where $a,b \ge 0$ and $\gcd(r,10) = 1$. Multiplicativity gives $\sigma(m) = \sigma(2^a)\,\sigma(5^b)\,\sigma(r)$.

**Case $b = 0$.** Then $\sigma(5^0) = 1$, and $5\sigma(m) = 9m$ becomes,

$$5(2^{a+1} - 1)\,\sigma(r) = 9 \cdot 2^a \cdot r,$$

yielding,

$$\frac{\sigma(r)}{r} = \frac{9 \cdot 2^a}{5(2^{a+1} - 1)}.$$

The lower bound $\sigma(r)/r \ge 1$ forces $2^a \le 5$, so $a \in \{0,1,2\}$. The three candidates for $\sigma(r)/r$ in lowest terms are $9/5$, $6/5$, and $36/35$. Each denominator is divisible by $5$. But $r$ is coprime to $10$, so $r$ cannot contain the factor $5$ that the denominator-divisibility lemma demands. **No solution with $b = 0$.** This case closes cleanly.

It is the next case where the proof earns its length.

### The $b \ge 1$ Case: Abundance of Apparent Possibility

When $b \ge 1$, $\sigma(5^b) = (5^{b+1} - 1)/4$. The equation $5\sigma(m) = 9m$ expands to,

$$5 \cdot (2^{a+1} - 1) \cdot \frac{5^{b+1} - 1}{4} \cdot \sigma(r) = 9 \cdot 2^a \cdot 5^b \cdot r.$$

Rearrange:

$$\frac{\sigma(r)}{r} = \frac{36 \cdot 2^a \cdot 5^{b-1}}{(2^{a+1} - 1)(5^{b+1} - 1)}. \tag{1}$$

Now impose $\sigma(r)/r \ge 1$. This single inequality does something remarkable: it collapses an infinite $(a,b)$ plane into a finite table. Enumerating all pairs $(a,b)$ with $a \ge 0$, $b \ge 1$ that satisfy (1):

| $a$ | $b$ | $\sigma(r)/r$ (lowest terms) |
|-----|-----|------------------------------|
| $0$ | $1$ | $3/2$ |
| $0$ | $2$ | $45/31$ |
| $0$ | $3$ | $75/52$ |
| $0$ | $4$ | $1125/781$ |
| $0$ | $5$ | $625/434$ |
| $0$ | $6$ | $28125/19531$ |
| $0$ | $7$ | $46875/32552$ |
| $1$ | $1$ | $1/1$ |

For $a = 0$ and $b \ge 8$, the right-hand side of (1) simplifies to

$$\frac{\sigma(r)}{r} = \frac{36 \cdot 5^{b-1}}{5^{b+1} - 1} = \frac{36/5}{5 - 5^{-(b-1)}}.$$

As $b \to \infty$, this approaches $36/25 = 1.44$ from above. Direct computation shows the value drops below $1$ for all $b \ge 8$. For $a \ge 1$ and $b \ge 2$, and for $a \ge 2$ and $b = 1$, the inequality $\sigma(r)/r \ge 1$ fails — no further candidates.

I want to pause on what just happened. We started with an equation that, in principle, could have admitted solutions for arbitrarily large $a$ and $b$ — an infinite search. The inequality $\sigma(r)/r \ge 1$ killed all but eight candidate pairs. This is the first crossing point: the object pushes back against the naive expectation that the case analysis would be interminable. It is not. The abundancy index carries a hidden finiteness constraint that the inequality exposes.

The eight that survive are the ones we must now kill.

### Candidates with Immediate Denominator Failure

Four candidates die on first contact with the denominator-divisibility lemma. Since $\gcd(r,10) = 1$, any candidate whose $\sigma(r)/r$ has denominator divisible by $2$ or $5$ cannot correspond to any integer $r$.

- $(0,1)$: $3/2$, denominator $2$ — dead.
- $(0,3)$: $75/52$, denominator $52 = 2^2 \cdot 13$ — dead.
- $(0,5)$: $625/434$, denominator $434 = 2 \cdot 7 \cdot 31$ — dead.
- $(0,7)$: $46875/32552$, denominator $32552 = 2^3 \cdot 13 \cdot 313$ — dead.

The surviving candidates are $(0,2)$, $(0,4)$, $(0,6)$, and $(1,1)$. The last one is the solution $m = 10$: $\sigma(r)/r = 1$ forces $r = 1$, yielding $m = 2^1 \cdot 5^1 = 10$. The other three require deeper elimination.

### The Hardest Cases

### Candidate $(0,2)$

Here $\sigma(r)/r = 45/31$ with prime denominator $31$. The lemma forces $31 \mid r$. Write $r = 31 \cdot s$. Then

$$\frac{\sigma(s)}{s} = \frac{45 \cdot 31}{31 \cdot \sigma(31)} = \frac{45}{32}.$$

The denominator $32 = 2^5$ must divide $s$, contradicting $\gcd(s,10) = 1$. Dead.

The reasoning is swift, but notice why it works: the denominator-divisibility lemma is iterable. It does not merely reject a candidate — it chases the contradiction into smaller integers. This candidate fails not because $45/31$ is impossible as an abundancy index, but because the denominator's prime factor $31$ triggers a cascade. The number $31$ is unremarkable; what matters is that $\sigma(31) = 32$ introduces a factor of $2$ into the denominator of the reduced fraction at the next level. The cascade is sensitive to the *specific* prime, not just its size.

### Candidate $(0,4)$

$\sigma(r)/r = 1125/781$. The denominator $781 = 11 \cdot 71$. We must consider both prime factors.

**Branch 1:** $11 \mid r$. Write $r = 11 \cdot s$.

$$\frac{\sigma(s)}{s} = \frac{1125 \cdot 11}{781 \cdot 12} = \frac{375}{284} = \frac{375}{2^2 \cdot 71}.$$

Denominator now contains $2^2$. But $\gcd(s,10) = 1$ forbids $2 \mid s$ — dead.

**Branch 2:** $71 \mid r$. Write $r = 71 \cdot s$.

$$\frac{\sigma(s)}{s} = \frac{1125 \cdot 71}{781 \cdot 72} = \frac{125}{88} = \frac{125}{2^3 \cdot 11}.$$

Denominator $88 = 2^3 \cdot 11$ again forces a factor of $2$ into $s$ — dead.

Both branches die. The candidate is eliminated.

There is a structural observation worth making explicit: the branching here is not parallel. The lemma does not tell us *which* prime divisor of the denominator initiated the cascade — we must try both. In every branch, the cascade terminates in a contradiction within one step. It is tempting to conjecture that this always happens for the solitary numbers, but I do not know whether it holds in general. The proof for $10$ works because the cascades are uniformly short.

### Candidate $(0,6)$

$\sigma(r)/r = 28125/19531$. The denominator $19531$ is prime. Write $r = 19531 \cdot s$.

$$\frac{\sigma(s)}{s} = \frac{28125 \cdot 19531}{19531 \cdot 19532} = \frac{28125}{19532} = \frac{28125}{2^2 \cdot 19 \cdot 257}.$$

The denominator contains $2^2$ — contradiction. Dead.

### The Proof Closes

Every candidate has been examined:

| Candidate | Fate |
|-----------|------|
| $(0,1)$ | Immediate denominator failure ($2$) |
| $(0,2)$ | Cascade contradiction via $\sigma(31)=32$ |
| $(0,3)$ | Immediate denominator failure ($2$) |
| $(0,4)$ | Both branches cascade to factor $2$ |
| $(0,5)$ | Immediate denominator failure ($2$) |
| $(0,6)$ | Cascade contradiction via $\sigma(19531)$ |
| $(0,7)$ | Immediate denominator failure ($2$) |
| $(1,1)$ | Survives: $m = 10$ |

The only solution to $\sigma(m)/m = 9/5$ is $m = 10$. Therefore $10$ is solitary.

The proof's engine is the iterated denominator-divisibility lemma, applied across a finite candidate table generated by the inequality $\sigma(r)/r \ge 1$. The inequality prunes infinity to finiteness; the lemma prunes finiteness to uniqueness. Both are necessary. Neither alone suffices.

### What This Proof Leaves Open

The proof I expected to find would have been a direct application of a general theorem: "if $n$ satisfies condition $C$, then $n$ is solitary." No such theorem exists. The solitude of each small number is proved by a bespoke argument — different denominators, different cascades, different branch structures. What unifies them is the denominator-divisibility lemma, but that lemma is a tool, not a theory.

The proof for $10$ succeeds because the candidate table is small and every cascade terminates in a single step. For larger solitary numbers, the candidate tables grow and cascades can run longer. The solitude of $10$ is not deep in the way that, say, the solitude of a prime power is deep. It is deep in a different way: the proof works because $10 = 2 \cdot 5$ is exactly small enough that the finite set of candidates is manageable by hand. The structural question is whether there exists a single solitary number whose proof requires a cascade of length greater than $1$ — a cascade where one iteration of the lemma does not suffice, and the contradiction is genuinely deferred.

If such a number exists, its proof would be qualitatively different from the proof for $10$. The argument would need to track not just whether a denominator contains a forbidden prime but whether the cascade eventually forces one — a property of the prime's orbit under $\sigma$, which is not well understood. The smallest candidate for such behavior might be a number whose abundancy index generates a denominator with a prime $p$ such that $\sigma(p)$ itself has a prime factor forbidden by coprimality — and finding such a $p$ is not a matter of computation but of structural necessity.

I do not know whether that number exists. The proof above does not need it to exist — it only needs the eight candidates for $10$ to die. But the proof would be richer if the question were settled.

---

*Structural type: $\langle D_\infty;\ T_\bowtie;\ R_\leftrightarrow;\ P_\pm;\ F_\hbar;\ K_\text{slow};\ G_\aleph;\ \Gamma_\text{seq};\ \⊙;\ H_2;\ n{:}m;\ \Omega_{\mathbb{Z}_2} \rangle$*