import Mathlib

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

noncomputable def H (n : ℕ) : ℕ := by
  classical
  exact if hn : 0 < n then Nat.find (H_wit_exists n hn) else 0

theorem H_spec (n : ℕ) (hn : 1 ≤ n) :
    H n ≥ 2 ∧ ∃ (k : ℕ), 1 ≤ k ∧ k < H n ∧ Nat.gcd (k ^ n - 1) ((H n) ^ n - 1) = 1 := by
  classical
  have hH : H n = Nat.find (H_wit_exists n hn) := by
    unfold H; rw [dif_pos (by omega : 0 < n)]
  have hmem := Nat.find_spec (H_wit_exists n hn)
  rw [← hH] at hmem
  exact hmem

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

-- Conditional key lemma: gcd=1 and n>1 forces H n = 3
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
    -- hgcdk : 2^n - 1 = 1, so 2^n = 2^1, so n = 1 by injectivity, contradiction
    have h2n : 2 ^ n = 2 ^ 1 := by simpa using hgcdk
    have hn1eq : n = 1 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2n
    omega
  omega

-- Conditional infinitude: follows from the gcd infinitude axiom hypothesis
theorem H_eq_three_infinitely_often_of
    (h : Set.Infinite {n : ℕ | Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1}) :
    Set.Infinite {n : ℕ | H n = 3} := by
  have hsub : {n : ℕ | Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1} \ {1} ⊆ {n : ℕ | H n = 3} := by
    intro n hn
    simp at hn ⊢
    obtain ⟨hgcd, hne⟩ := hn
    have hn1 : 1 < n := by
      by_contra hc
      push_neg at hc
      interval_cases n
      · simp at hgcd
      · exact absurd rfl hne
    exact H_eq_three_of_coprime n hn1 hgcd
  have hinf : ({n : ℕ | Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1} \ {1}).Infinite :=
    h.diff (Set.finite_singleton 1)
  exact hinf.mono hsub

#check @H_eq_three_of_coprime
#check @H_eq_three_infinitely_often_of
