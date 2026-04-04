import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1609

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f+1⟩ => some ⟨a, b+3, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ a c f,
    ⟨a, 0, c, k, 0, f⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a c f
  · ring_nf; finish
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (c + 1) f)
    ring_nf; finish

theorem inner_loop : ∀ M, ∀ a D E F,
    ⟨a, 0, 3 * M, D, E + 1, F + M⟩ [fm]⊢* ⟨a, 0, 0, D + 3 * M, E + 2 * M + 1, F⟩ := by
  intro M; induction' M with M ih <;> intro a D E F
  · ring_nf; finish
  · have h1 : fm ⟨a, 0, 3 * (M + 1), D, E + 1, F + (M + 1)⟩ =
      some ⟨a, 3, 3 * (M + 1), D, E, F + M⟩ := by simp [fm]
    have h2 : fm ⟨a, 3, 3 * (M + 1), D, E, F + M⟩ =
      some ⟨a, 2, 3 * M + 2, D + 1, E + 1, F + M⟩ := by simp [fm]
    have h3 : fm ⟨a, 2, 3 * M + 2, D + 1, E + 1, F + M⟩ =
      some ⟨a, 1, 3 * M + 1, D + 2, E + 2, F + M⟩ := by simp [fm]
    have h4 : fm ⟨a, 1, 3 * M + 1, D + 2, E + 2, F + M⟩ =
      some ⟨a, 0, 3 * M, D + 3, E + 3, F + M⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h1)
    apply stepStar_trans (step_stepStar h2)
    apply stepStar_trans (step_stepStar h3)
    apply stepStar_trans (step_stepStar h4)
    apply stepStar_trans (ih a (D + 3) (E + 2) F)
    ring_nf; finish

theorem tail_loop : ∀ K, ∀ a D F,
    ⟨a, 0, 0, D, K, F + 1⟩ [fm]⊢* ⟨a + 3 * K, 0, 0, D + 3 * K, 0, F + 2 * K + 1⟩ := by
  intro K; induction' K with K ih <;> intro a D F
  · ring_nf; finish
  · have h1 : fm ⟨a, 0, 0, D, K + 1, F + 1⟩ =
      some ⟨a, 3, 0, D, K, F⟩ := by simp [fm]
    have h2 : fm ⟨a, 3, 0, D, K, F⟩ =
      some ⟨a + 1, 2, 0, D + 1, K, F + 1⟩ := by simp [fm]
    have h3 : fm ⟨a + 1, 2, 0, D + 1, K, F + 1⟩ =
      some ⟨a + 2, 1, 0, D + 2, K, F + 2⟩ := by simp [fm]
    have h4 : fm ⟨a + 2, 1, 0, D + 2, K, F + 2⟩ =
      some ⟨a + 3, 0, 0, D + 3, K, F + 3⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h1)
    apply stepStar_trans (step_stepStar h2)
    apply stepStar_trans (step_stepStar h3)
    apply stepStar_trans (step_stepStar h4)
    apply stepStar_trans (ih (a + 3) (D + 3) (F + 2))
    ring_nf; finish

theorem main_trans (N H M : ℕ) (hM : 2 * H + N = 3 * M) :
    ⟨2 * H + 1, 0, 0, 2 * H + N + 1, 0, N + H + 1⟩ [fm]⊢⁺
    ⟨6 * H + 2 * N + 3, 0, 0, 6 * H + 3 * N + 4, 0, 2 * N + 3 * H + 3⟩ := by
  apply stepStar_stepPlus_stepPlus
    (r4_drain (2 * H + N + 1) (2 * H + 1) 0 (N + H + 1))
  rw [show (0 : ℕ) + (2 * H + N + 1) = 2 * H + N + 1 from by ring]
  have hR5 : fm ⟨2 * H + 1, 0, 2 * H + N + 1, 0, 0, N + H + 1⟩ =
    some ⟨2 * H, 1, 2 * H + N + 1, 0, 0, N + H + 1⟩ := by simp [fm]
  apply step_stepStar_stepPlus hR5
  have hR1 : fm ⟨2 * H, 1, 2 * H + N + 1, 0, 0, N + H + 1⟩ =
    some ⟨2 * H, 0, 2 * H + N, 1, 1, N + H + 1⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar hR1)
  rw [hM, show (1 : ℕ) = 0 + 1 from rfl,
      show N + H + 1 = (N + H + 1 - M) + M from by omega]
  apply stepStar_trans (inner_loop M (2 * H) 1 0 (N + H + 1 - M))
  rw [show (0 : ℕ) + 2 * M + 1 = 2 * M + 1 from by ring,
      show N + H + 1 - M = (N + H - M) + 1 from by omega,
      show 1 + 3 * M = 3 * M + 1 from by ring]
  apply stepStar_trans (tail_loop (2 * M + 1) (2 * H) (3 * M + 1) (N + H - M))
  rw [show 2 * H + 3 * (2 * M + 1) = 6 * H + 2 * N + 3 from by omega,
      show 3 * M + 1 + 3 * (2 * M + 1) = 6 * H + 3 * N + 4 from by omega,
      show N + H - M + 2 * (2 * M + 1) + 1 = 2 * N + 3 * H + 3 from by omega]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ N H, q = ⟨2 * H + 1, 0, 0, 2 * H + N + 1, 0, N + H + 1⟩ ∧ 3 ∣ (2 * H + N))
  · intro q ⟨N, H, hq, ⟨M, hM⟩⟩
    refine ⟨⟨6 * H + 2 * N + 3, 0, 0, 6 * H + 3 * N + 4, 0, 2 * N + 3 * H + 3⟩,
      ⟨N + 1, N + 3 * H + 1, ?_, ?_⟩,
      hq ▸ main_trans N H M hM⟩
    · show (6 * H + 2 * N + 3, (0 : ℕ), (0 : ℕ), 6 * H + 3 * N + 4, (0 : ℕ), 2 * N + 3 * H + 3) =
        (2 * (N + 3 * H + 1) + 1, 0, 0, 2 * (N + 3 * H + 1) + (N + 1) + 1, 0,
          N + 1 + (N + 3 * H + 1) + 1)
      simp only [Prod.mk.injEq]
      exact ⟨by ring, trivial, trivial, by ring, trivial, by ring⟩
    · exact ⟨3 * M + 1, by omega⟩
  · exact ⟨0, 0, rfl, ⟨0, by ring⟩⟩

end Sz22_2003_unofficial_1609
