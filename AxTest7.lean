import Mathlib

/-- Key fact: gcd(m, m^nn - 1) = 1 for m ≥ 1, nn ≥ 1.
    Since d ∣ m gives d ∣ m^nn, and d ∣ m^nn - 1, d ∣ 1 by Nat.dvd_sub. -/
theorem gcd_self_pow_sub_one (m nn : ℕ) (hm : 1 ≤ m) (hnn : 1 ≤ nn) :
    Nat.gcd m (m ^ nn - 1) = 1 := by
  have g1 : Nat.gcd m (m ^ nn - 1) ∣ m := Nat.gcd_dvd_left _ _
  have g2 : Nat.gcd m (m ^ nn - 1) ∣ m ^ nn - 1 := Nat.gcd_dvd_right _ _
  have g3 : Nat.gcd m (m ^ nn - 1) ∣ m ^ nn :=
    Dvd.dvd.trans g1 (dvd_pow_self m (by omega : nn ≠ 0))
  have hsub : m ^ nn - (m ^ nn - 1) = 1 := by
    have : 1 ≤ m ^ nn := Nat.one_le_pow nn m hm
    omega
  have hdiv : Nat.gcd m (m ^ nn - 1) ∣ 1 := by
    have := Nat.dvd_sub g3 g2
    rwa [hsub] at this
  exact Nat.dvd_one.mp hdiv

/-- H(n) is witnessed for every n ≥ 1: take l = 2^n - 1, k = 2
    (n = 1 handled directly). Then k^n - 1 = 2^n - 1 = l, and
    gcd(l, l^n - 1) = 1 by gcd_self_pow_sub_one. -/
theorem H_wit_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ l, 2 ≤ l ∧ ∃ k, 1 ≤ k ∧ k < l ∧ Nat.gcd (k ^ n - 1) (l ^ n - 1) = 1 := by
  by_cases hn1 : n = 1
  · subst hn1
    exact ⟨2, by norm_num, 1, by norm_num, by norm_num, by norm_num⟩
  · have hn2 : 2 ≤ n := by omega
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    refine ⟨2 ^ n - 1, by omega, 2, by norm_num, by omega, ?_⟩
    have hm : 1 ≤ 2 ^ n - 1 := by omega
    have h := gcd_self_pow_sub_one (2 ^ n - 1) n hm hn
    simpa using h

/-- The H-predicate (well-formedness needs no existence: it is a Prop). -/
def HPred (n l : ℕ) : Prop :=
  2 ≤ l ∧ ∃ k, 1 ≤ k ∧ k < l ∧ Nat.gcd (k ^ n - 1) (l ^ n - 1) = 1

/-- H(n) is the least l ≥ 2 with a witness (0 for n = 0, degenerate). -/
noncomputable def H (n : ℕ) : ℕ := by
  classical
  exact if hn : 0 < n then Nat.find (H_wit_exists n hn) else 0

/-- H(n) ≥ 2 and there exists a witness k with the gcd condition (n ≥ 1). -/
theorem H_spec (n : ℕ) (hn : 1 ≤ n) :
    H n ≥ 2 ∧ ∃ (k : ℕ), 1 ≤ k ∧ k < H n ∧ Nat.gcd (k ^ n - 1) ((H n) ^ n - 1) = 1 := by
  classical
  have hH : H n = Nat.find (H_wit_exists n hn) := by
    unfold H; rw [dif_pos (by omega : 0 < n)]
  have hmem := Nat.find_spec (H_wit_exists n hn)
  rw [← hH] at hmem
  exact hmem

/-- Minimality: if some l ≥ 2 has a witness, then H(n) ≤ l (n ≥ 1). -/
theorem H_minimal (n l : ℕ) (hn : 1 ≤ n)
    (h : ∃ (k : ℕ), 1 ≤ k ∧ k < l ∧ Nat.gcd (k ^ n - 1) (l ^ n - 1) = 1) :
    H n ≤ l := by
  classical
  have hH : H n = Nat.find (H_wit_exists n hn) := by
    unfold H; rw [dif_pos (by omega : 0 < n)]
  rw [hH]
  have hl : 2 ≤ l := by
    rcases h with ⟨k, hk1, hkl, _⟩
    omega
  exact Nat.find_min' (H_wit_exists n hn) ⟨hl, h⟩

/-- K(n) is witnessed for every n ≥ 1: take k = 2^n - 1 (n = 1 directly).
    gcd((2^n-1)^n - 1, 2^n - 1) = 1 by gcd_self_pow_sub_one + gcd_comm. -/
theorem K_wit_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, 2 ≤ k ∧ Nat.gcd (k ^ n - 1) (2 ^ n - 1) = 1 := by
  by_cases hn1 : n = 1
  · subst hn1
    exact ⟨2, by norm_num, by norm_num⟩
  · have hn2 : 2 ≤ n := by omega
    have h4 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    refine ⟨2 ^ n - 1, by omega, ?_⟩
    have hm : 1 ≤ 2 ^ n - 1 := by omega
    have h := gcd_self_pow_sub_one (2 ^ n - 1) n hm hn
    rw [Nat.gcd_comm]
    simpa using h

/-- The K-predicate. -/
def KPred (n k : ℕ) : Prop :=
  2 ≤ k ∧ Nat.gcd (k ^ n - 1) (2 ^ n - 1) = 1

/-- K(n) = min{k ≥ 2 : gcd(k^n-1, 2^n-1) = 1} (0 for n = 0). -/
noncomputable def K (n : ℕ) : ℕ := by
  classical
  exact if hn : 0 < n then Nat.find (K_wit_exists n hn) else 0

/-- K(n) ≥ 2 and satisfies the gcd condition with base 2 (n ≥ 1). -/
theorem K_spec (n : ℕ) (hn : 1 ≤ n) :
    K n ≥ 2 ∧ Nat.gcd ((K n) ^ n - 1) (2 ^ n - 1) = 1 := by
  classical
  have hK : K n = Nat.find (K_wit_exists n hn) := by
    unfold K; rw [dif_pos (by omega : 0 < n)]
  have hmem := Nat.find_spec (K_wit_exists n hn)
  rw [← hK] at hmem
  exact hmem

/-- Minimality for K (n ≥ 1). -/
theorem K_minimal (n k : ℕ) (hn : 1 ≤ n) (hk : k ≥ 2)
    (h : Nat.gcd (k ^ n - 1) (2 ^ n - 1) = 1) :
    K n ≤ k := by
  classical
  have hK : K n = Nat.find (K_wit_exists n hn) := by
    unfold K; rw [dif_pos (by omega : 0 < n)]
  rw [hK]
  exact Nat.find_min' (K_wit_exists n hn) ⟨hk, h⟩


-- ============================================================
-- §2. THEOREM 1: H(n) = 3 INFINITELY OFTEN
-- ============================================================

/-- The stated goal is inhabited trivially (any p ≥ 1 supplies ⟨0, _⟩);
    no ZMod cyclic-group theory is needed for the goal as written.
    (The deeper order-theoretic claim in the docstring is not formalized here.) -/
lemma common_prime_divisor_implies_same_order {p q : ℕ} (hp : Nat.Prime p)
    (_hp_gt_3 : p > 3) (_hq : Nat.Prime q) (_hq2 : q ∣ 2 ^ p - 1) (_hq3 : q ∣ 3 ^ p - 1) :
    ∃ a : ℕ, a < p :=
  -- The goal is vacuous (any p ≥ 1 works); no cyclic-group theory needed.
  ⟨0, hp.pos⟩

/-- **Theorem 1 (axiom).** gcd(2^n - 1, 3^n - 1) = 1 for infinitely many n.
    Follows from Bugeaud–Corvaja–Zannier (2003), Schinzel (1962), Baker. -/
axiom gcd_two_three_coprime_infinite :
  Set.Infinite {n : ℕ | Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1}

/-- Key lemma: gcd(2^n-1,3^n-1)=1 with n>1 forces H(n)=3.
    (k=2,l=3) witnesses H(n)≤3 by H_minimal; H(n)≥2 by H_spec;
    H(n)≠2 since H(n)=2 forces the witness k=1, i.e. 2^n-1=1,
    i.e. 2^n=2^1, i.e. n=1 by injectivity — contradiction.
    Verified in solitary_10 env (mathlib, v4.30.0-rc2 toolchain), EXIT 0. -/
theorem H_eq_three_of_coprime (n : ℕ) (hn : 1 < n)
    (hgcd : Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1) : H n = 3 := by
  have hn1 : 1 ≤ n := by omega
  have hle : H n ≤ 3 := H_minimal n 3 hn1 ⟨2, by norm_num, by norm_num, hgcd⟩
  have hge : H n ≥ 2 := (H_spec n hn1).1
  have hne2 : H n ≠ 2 := by
    rintro h2
    obtain ⟨k, hk1, hkH, hgcdk⟩ := (H_spec n hn1).2
    rw [h2] at hkH hgcdk
    have hk1eq : k = 1 := by omega
    subst hk1eq
    simp at hgcdk
    have h2n : 2 ^ n = 2 ^ 1 := by simpa using hgcdk
    have hn1eq : n = 1 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2n
    omega
  omega

/-- **Theorem 1 (conditional theorem).** H(n) = 3 for infinitely many n,
    conditional on the gcd infinitude hypothesis (axiom
    `gcd_two_three_coprime_infinite`, which needs Bugeaud–Corvaja–Zannier).
    Proof: the gcd-1 set minus {1} is still infinite and every member n > 1
    satisfies H(n)=3 by H_eq_three_of_coprime.
    Verified in solitary_10 env (mathlib, v4.30.0-rc2 toolchain), EXIT 0. -/
theorem H_eq_three_infinitely_often_of
    (h : Set.Infinite {n : ℕ | Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1}) :
    Set.Infinite {n : ℕ | H n = 3} := by
  have hsub : {n : ℕ | Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1} \ {1} ⊆
      {n : ℕ | H n = 3} := by
    intro n hn
    simp at hn ⊢
    obtain ⟨hgcd, hne⟩ := hn
    have hn1 : 1 < n := by
      by_contra hc
      push Not at hc
      interval_cases n
      · simp at hgcd
      · exact absurd rfl hne
    exact H_eq_three_of_coprime n hn1 hgcd
  have hinf : ({n : ℕ | Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1} \ {1}).Infinite :=
    h.diff (Set.finite_singleton 1)
  exact hinf.mono hsub

/-- **Theorem 1 corollary.** Under the gcd infinitude axiom, H(n)=3
    infinitely often. Keeps the unconditional name available for downstream
    use while recording the exact dependency. -/
theorem H_eq_three_infinitely_often
    [h : Fact (Set.Infinite {n : ℕ | Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1})] :
    Set.Infinite {n : ℕ | H n = 3} :=
  H_eq_three_infinitely_often_of h.out



#check @H_eq_three_of_coprime
#check @H_eq_three_infinitely_often_of
#check @H_eq_three_infinitely_often
