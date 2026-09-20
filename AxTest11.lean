import Mathlib

def f_tot_iter (n : ℕ) : ℕ := Nat.totient n + 1

theorem totient_terminates (n : ℕ) (h : n > 1) :
    ∃ p : ℕ, Nat.Prime p ∧ ∃ k : ℕ, (Nat.iterate f_tot_iter k n) = p := by
  -- Strong induction: f shrinks non-primes, fixes primes.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hprime : Nat.Prime n
    · exact ⟨n, hprime, 0, rfl⟩
    · -- n composite, n > 1: φ(n) ≤ n-2, so f(n) < n and f(n) > 1
      have hlt : Nat.totient n < n := Nat.totient_lt n h
      have hne : Nat.totient n ≠ n - 1 := by
        intro hcon
        apply hprime
        have hpos : 0 < n := by omega
        exact (Nat.totient_eq_iff_prime hpos).mp hcon
      have hle : Nat.totient n ≤ n - 2 := by omega
      have hfn_lt : f_tot_iter n < n := by simp [f_tot_iter]; omega
      have hfn_gt : f_tot_iter n > 1 := by
        have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
        simp [f_tot_iter]; omega
      obtain ⟨p, hp, k, hk⟩ := ih (f_tot_iter n) hfn_lt hfn_gt
      exact ⟨p, hp, k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

#check @totient_terminates
