import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1921: [9/70, 2/15, 275/2, 7/11, 4/7]

Vector representation:
```
-1  2 -1 -1  0
 1 -1 -1  0  0
-1  0  2  0  1
 0  0  0  1 -1
 2  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1921

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    apply stepStar_trans (step_stepStar (show (⟨k + 1, 0, c, 0, e⟩ : Q) [fm]⊢ ⟨k, 0, c + 2, 0, e + 1⟩ from by simp [fm]))
    apply stepStar_trans (ih (c + 2) (e + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ k b c d,
    ⟨0, b + 1, c + 2 * k, d + k, 0⟩ [fm]⊢* ⟨0, b + k + 1, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    apply stepStar_trans (step_stepStar (show (⟨0, b + 1, c + 2 * k + 2, d + k + 1, 0⟩ : Q) [fm]⊢ ⟨1, b, c + 2 * k + 1, d + k + 1, 0⟩ from by simp [fm]))
    apply stepStar_trans (step_stepStar (show (⟨1, b, c + 2 * k + 1, d + k + 1, 0⟩ : Q) [fm]⊢ ⟨0, b + 2, c + 2 * k, d + k, 0⟩ from by simp [fm]))
    apply stepStar_trans (ih (b + 1) c d)
    ring_nf; finish

theorem odd_tail : ∀ b d, ⟨0, b + 2, 1, d + 1, 0⟩ [fm]⊢* ⟨0, b + 2, 0, d + 1, 0⟩ := by
  intro b d; execute fm 5

theorem sub_cycle_step : ∀ b d, ⟨0, b + 1, 0, d + 3, 0⟩ [fm]⊢* ⟨0, b + 3, 0, d + 2, 0⟩ := by
  intro b d; execute fm 9

theorem sub_cycle : ∀ k b d,
    ⟨0, b + 1, 0, d + k + 2, 0⟩ [fm]⊢* ⟨0, b + 2 * k + 1, 0, d + 2, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) + 2 = (d + 1) + k + 2 from by ring]
    apply stepStar_trans (ih b (d + 1))
    rw [show d + 1 + 2 = d + 3 from by ring,
        show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    apply stepStar_trans (sub_cycle_step (b + 2 * k) d)
    ring_nf; finish

theorem exit_preamble : ∀ b, ⟨0, b + 1, 0, 2, 0⟩ [fm]⊢⁺ ⟨2, b, 0, 0, 2⟩ := by
  intro b; execute fm 7

theorem kb_drain : ∀ b k,
    ⟨k + 1, b, 0, 0, k + 1⟩ [fm]⊢* ⟨0, 0, b + 2 * k + 2, 0, b + 2 * k + 2⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ihb; intro k
  rcases b with _ | _ | b
  · -- b = 0
    rw [show (0 : ℕ) + 2 * k + 2 = 0 + 2 * (k + 1) from by ring]
    apply stepStar_trans (r3_chain (k + 1) 0 (k + 1))
    ring_nf; finish
  · -- b = 1
    rw [show (1 : ℕ) + 2 * k + 2 = 3 + 2 * k from by ring]
    apply stepStar_trans (step_stepStar (show (⟨k + 1, 1, 0, 0, k + 1⟩ : Q) [fm]⊢ ⟨k, 1, 2, 0, k + 2⟩ from by simp [fm]))
    apply stepStar_trans (step_stepStar (show (⟨k, 1, 2, 0, k + 2⟩ : Q) [fm]⊢ ⟨k + 1, 0, 1, 0, k + 2⟩ from by simp [fm]))
    apply stepStar_trans (step_stepStar (show (⟨k + 1, 0, 1, 0, k + 2⟩ : Q) [fm]⊢ ⟨k, 0, 3, 0, k + 3⟩ from by simp [fm]))
    apply stepStar_trans (r3_chain k 3 (k + 3))
    ring_nf; finish
  · -- b + 2
    rw [show b + 2 + 2 * k + 2 = b + 2 * (k + 1) + 2 from by ring]
    apply stepStar_trans (step_stepStar (show (⟨k + 1, b + 2, 0, 0, k + 1⟩ : Q) [fm]⊢ ⟨k, b + 2, 2, 0, k + 2⟩ from by simp [fm]))
    apply stepStar_trans (step_stepStar (show (⟨k, b + 2, 2, 0, k + 2⟩ : Q) [fm]⊢ ⟨k + 1, b + 1, 1, 0, k + 2⟩ from by simp [fm]))
    apply stepStar_trans (step_stepStar (show (⟨k + 1, b + 1, 1, 0, k + 2⟩ : Q) [fm]⊢ ⟨k + 1 + 1, b, 0, 0, k + 2⟩ from by simp [fm]))
    rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    apply stepStar_trans (ihb b (by omega) (k + 1))
    ring_nf; finish

theorem even_trans :
    ⟨0, 0, 2 * n + 8, 2 * n + 8, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * n + 10, 3 * n + 10, 0⟩ := by
  step fm; step fm; step fm
  rw [show 2 * n + 6 = 0 + 2 * (n + 3) from by ring,
      show 2 * n + 5 = (n + 2) + (n + 3) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r2r1_chain (n + 3) 3 0 (n + 2))
  rw [show 3 + (n + 3) + 1 = n + 6 + 1 from by ring,
      show n + 2 = 0 + n + 2 from by ring,
      show n + 6 + 1 = (n + 6) + 1 from by ring]
  apply stepStar_trans (sub_cycle n (n + 6) 0)
  rw [show 0 + 2 = 2 from by ring,
      show n + 6 + 2 * n + 1 = (3 * n + 6) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (exit_preamble (3 * n + 6)))
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (kb_drain (3 * n + 6) 1)
  rw [show 3 * n + 6 + 2 * 1 + 2 = 3 * n + 10 from by ring]
  have h := e_to_d (3 * n + 10) 0 (c := 3 * n + 10)
  simp at h; exact h

theorem odd_trans :
    ⟨0, 0, 2 * n + 7, 2 * n + 7, 0⟩ [fm]⊢⁺ ⟨0, 0, 3 * n + 9, 3 * n + 9, 0⟩ := by
  step fm; step fm; step fm
  rw [show 2 * n + 5 = 1 + 2 * (n + 2) from by ring,
      show 2 * n + 4 = (n + 2) + (n + 2) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r2r1_chain (n + 2) 3 1 (n + 2))
  rw [show 3 + (n + 2) + 1 = (n + 4) + 2 from by ring,
      show n + 2 = (n + 1) + 1 from by ring]
  apply stepStar_trans (odd_tail (n + 4) (n + 1))
  rw [show (n + 4) + 2 = n + 5 + 1 from by ring,
      show (n + 1) + 1 = 0 + n + 2 from by ring]
  apply stepStar_trans (sub_cycle n (n + 5) 0)
  rw [show 0 + 2 = 2 from by ring,
      show n + 5 + 2 * n + 1 = (3 * n + 5) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (exit_preamble (3 * n + 5)))
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (kb_drain (3 * n + 5) 1)
  rw [show 3 * n + 5 + 2 * 1 + 2 = 3 * n + 9 from by ring]
  have h := e_to_d (3 * n + 9) 0 (c := 3 * n + 9)
  simp at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 10, 10, 0⟩) (by execute fm 187)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ C, C ≥ 7 ∧ q = ⟨0, 0, C, C, 0⟩)
  · intro c ⟨C, hC, hq⟩; subst hq
    rcases Nat.even_or_odd C with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨n, rfl⟩ : ∃ n, K = n + 4 := ⟨K - 4, by omega⟩
      exact ⟨⟨0, 0, 3 * n + 10, 3 * n + 10, 0⟩,
        ⟨3 * n + 10, by omega, rfl⟩, even_trans⟩
    · subst hK
      obtain ⟨n, rfl⟩ : ∃ n, K = n + 3 := ⟨K - 3, by omega⟩
      refine ⟨⟨0, 0, 3 * n + 9, 3 * n + 9, 0⟩,
        ⟨3 * n + 9, by omega, rfl⟩, ?_⟩
      show ⟨0, 0, 2 * (n + 3) + 1, 2 * (n + 3) + 1, 0⟩ [fm]⊢⁺ _
      rw [show 2 * (n + 3) + 1 = 2 * n + 7 from by ring]
      exact odd_trans
  · exact ⟨10, by omega, rfl⟩
