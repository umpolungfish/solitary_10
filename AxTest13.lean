import Mathlib
namespace Imscribing.ManuscriptSpine.Questions
theorem banach_steinhaus {E F : Type _} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [CompleteSpace E] [NormedSpace ℝ E] [NormedSpace ℝ F]
  (T : ℕ → E →L[ℝ] F) (h : ∀ x, BddAbove (Set.range (fun n => ‖T n x‖))) :
  BddAbove (Set.range (fun n => ‖T n‖)) := by
  have h' : ∀ x, ∃ C, ∀ i, ‖T i x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := h x
    refine ⟨C, fun i => ?_⟩
    exact hC (Set.mem_range_self i)
  obtain ⟨C', hC'⟩ := _root_.banach_steinhaus h'
  exact ⟨C', by rintro _ ⟨i, rfl⟩; exact hC' i⟩
#check @banach_steinhaus
end Imscribing.ManuscriptSpine.Questions
