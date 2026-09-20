import Mathlib

def distinct_subset_sums (A : Finset ℕ) : Prop :=
  ∀ (s t : Finset ℕ), s ⊆ A → t ⊆ A → s.sum id = t.sum id → s = t

theorem max_distinct_subset_sums_count (n : ℕ)
    (A : Finset ℕ) (hmem : ∀ a ∈ A, a ≤ n) (hd : distinct_subset_sums A) :
    2 ^ A.card ≤ A.card * n + 1 := by
  have hpow : (A.powerset).card = 2 ^ A.card := Finset.card_powerset A
  have hinj : Set.InjOn (fun s => s.sum id) (↑A.powerset : Set (Finset ℕ)) := by
    intro s hs t ht hst
    have hs' : s ∈ A.powerset := by simpa using hs
    have ht' : t ∈ A.powerset := by simpa using ht
    exact hd s t (Finset.mem_powerset.mp hs') (Finset.mem_powerset.mp ht') hst
  have himg : ((A.powerset).image (fun s => s.sum id)).card = 2 ^ A.card := by
    rw [Finset.card_image_of_injOn hinj, hpow]
  have hsub : (A.powerset).image (fun s => s.sum id) ⊆ Finset.Icc 0 (A.card * n) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx ⊢
    obtain ⟨s, hs, rfl⟩ := hx
    have hsA : s ⊆ A := Finset.mem_powerset.mp hs
    have hle : s.sum id ≤ A.card * n := by
      have h1 : s.sum id ≤ s.card * n := by
        calc s.sum id ≤ s.sum (fun _ => n) :=
              Finset.sum_le_sum (fun a ha => hmem a (hsA ha))
          _ = s.card * n := by simp [Finset.sum_const, smul_eq_mul]
      have h2 : s.card ≤ A.card := Finset.card_le_card hsA
      calc s.sum id ≤ s.card * n := h1
        _ ≤ A.card * n := Nat.mul_le_mul_right n h2
    exact ⟨Nat.zero_le _, hle⟩
  have hle2 : ((A.powerset).image (fun s => s.sum id)).card ≤ (Finset.Icc 0 (A.card * n)).card :=
    Finset.card_le_card hsub
  have hcard : (Finset.Icc 0 (A.card * n)).card = A.card * n + 1 := by simp
  omega

#check @max_distinct_subset_sums_count
