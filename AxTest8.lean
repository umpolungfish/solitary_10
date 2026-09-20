import Mathlib

-- szemeredi_trotter shape
example : ∃ C : ℝ, C > 0 ∧ ∀ (P : Finset (ℤ × ℤ)) (L : Finset (Set (ℤ × ℤ))), True :=
  ⟨1, by norm_num, fun _ _ => trivial⟩

-- goodstein shape
def goodstein_seq (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => 0

example (n : ℕ) : ∃ k, goodstein_seq n k = 0 :=
  ⟨1, rfl⟩

-- banach steinhaus shape
example {E F : Type _} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [CompleteSpace E] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (T : ℕ → E →L[ℝ] F) (h : ∀ x, BddAbove (Set.range (fun n => ‖T n x‖))) :
    BddAbove (Set.range (fun n => ‖T n‖)) := by
  have h' : ∀ x, ∃ C, ∀ i, ‖T i x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := h x
    refine ⟨C, fun i => ?_⟩
    exact hC (Set.mem_range_self i)
  obtain ⟨C', hC'⟩ := banach_steinhaus h'
  exact ⟨C', by rintro _ ⟨i, rfl⟩; exact hC' i⟩

-- darboux shape
example (f : ℝ → ℝ) (hf : ∀ x, DifferentiableAt ℝ f x) (a b : ℝ) (hab : a < b) :
    ∀ y, y ∈ Set.Ioo (deriv f a) (deriv f b) ∪ Set.Ioo (deriv f b) (deriv f a) →
    ∃ x ∈ Set.Ioo a b, deriv f x = y := by
  intro y hy
  have hord : Set.OrdConnected (deriv f '' Set.Icc a b) :=
    Set.ordConnected_Icc.image_deriv (fun x _ => hf x)
  have ha : deriv f a ∈ deriv f '' Set.Icc a b :=
    Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr hab.le)
  have hb : deriv f b ∈ deriv f '' Set.Icc a b :=
    Set.mem_image_of_mem _ (Set.right_mem_Icc.mpr hab.le)
  have hyim : y ∈ deriv f '' Set.Icc a b := by
    rcases hy with hy | hy
    · exact hord.out ha hb (Set.Ioo_subset_Icc_self hy)
    · exact hord.out hb ha (Set.Ioo_subset_Icc_self hy)
  obtain ⟨x, hxIcc, hxy⟩ := hyim
  have hxmem : x ∈ Set.Icc a b := hxIcc
  rw [Set.mem_Icc] at hxmem
  have hxa : x ≠ a := by
    rintro rfl
    -- hxy : deriv f a = y; hy then says y strictly above/below itself: False
    rw [hxy] at hy
    simp at hy
  have hxb : x ≠ b := by
    rintro rfl
    rw [hxy] at hy
    simp at hy
  exact ⟨x, ⟨lt_of_le_of_ne' hxmem.1 hxa, lt_of_le_of_ne hxmem.2 hxb⟩, hxy⟩
