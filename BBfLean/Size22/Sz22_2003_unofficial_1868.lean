import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1868: [9/35, 25/33, 22/5, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  2  0 -1
 1  0 -1  0  1
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1868

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem r3_chain : ∀ k a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring]; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

theorem e_to_d : ∀ k a d e, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]; step fm
    apply stepStar_trans (ih a (d + 1) e); ring_nf; finish

theorem r3r2_chain : ∀ k a b c, ⟨a, b + k, c + 1, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + k + 1, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show b + (k + 1) = b + k + 1 from by ring]; step fm; step fm
    apply stepStar_trans (ih (a + 1) b (c + 1)); ring_nf; finish

theorem drain_step : ∀ a b d, ⟨a + 1, b, 0, d + 3, 0⟩ [fm]⊢* ⟨a, b + 5, 0, d, 0⟩ := by
  intro a b d; step fm; step fm; step fm; step fm; step fm; finish

theorem drain_rounds : ∀ k a b d, ⟨a + k, b, 0, d + 3 * k, 0⟩ [fm]⊢* ⟨a, b + 5 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring]
    apply stepStar_trans (ih (a + 1) b (d + 3))
    apply stepStar_trans (drain_step a (b + 5 * k) d)
    ring_nf; finish

theorem base_d2 : ∀ a b, ⟨a + 1, b, 0, 2, 0⟩ [fm]⊢* ⟨a, b + 3, 1, 0, 0⟩ := by
  intro a b; step fm; step fm; step fm; step fm; finish

theorem base_d1 : ∀ a b, ⟨a + 1, b, 0, 1, 0⟩ [fm]⊢* ⟨a, b + 1, 2, 0, 0⟩ := by
  intro a b; step fm; step fm; step fm; finish

theorem base_d0 : ∀ a b, ⟨a + 1, b + 1, 0, 0, 0⟩ [fm]⊢* ⟨a, b, 3, 0, 0⟩ := by
  intro a b; step fm; step fm; finish

theorem r3_first_step : ⟨a, 0, c + 1, 0, e⟩ [fm]⊢ ⟨a + 1, 0, c, 0, e + 1⟩ := by
  simp [fm]

theorem trans_r2 : ⟨a + 1, 0, 3 * K + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + 7 * K + 5, 0, 5 * K + 4, 0, 0⟩ := by
  rw [show 3 * K + 2 = (3 * K + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (r3_first_step (a := a + 1) (c := 3 * K + 1) (e := 0))
  rw [show a + 1 + 1 = a + 2 from by ring, show 0 + 1 = 1 from by ring,
      show 3 * K + 1 = 0 + (3 * K + 1) from by ring]
  apply stepStar_trans (r3_chain (3 * K + 1) (a + 2) 0 1)
  rw [show a + 2 + (3 * K + 1) = a + 3 * K + 3 from by ring,
      show 1 + (3 * K + 1) = 0 + (3 * K + 2) from by ring]
  apply stepStar_trans (e_to_d (3 * K + 2) (a + 3 * K + 3) 0 0)
  rw [show 0 + (3 * K + 2) = 2 + 3 * K from by ring,
      show a + 3 * K + 3 = (a + 2 * K + 3) + K from by ring]
  apply stepStar_trans (drain_rounds K (a + 2 * K + 3) 0 2)
  rw [show 0 + 5 * K = 5 * K from by ring,
      show a + 2 * K + 3 = (a + 2 * K + 2) + 1 from by ring]
  apply stepStar_trans (base_d2 (a + 2 * K + 2) (5 * K))
  rw [show 5 * K + 3 = 0 + (5 * K + 3) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (5 * K + 3) (a + 2 * K + 2) 0 0)
  ring_nf; finish

theorem trans_r1 : ⟨a + 1, 0, 3 * (K + 1) + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 7 * K + 9, 0, 5 * K + 8, 0, 0⟩ := by
  rw [show 3 * (K + 1) + 1 = (3 * K + 3) + 1 from by ring]
  apply step_stepStar_stepPlus (r3_first_step (a := a + 1) (c := 3 * K + 3) (e := 0))
  rw [show a + 1 + 1 = a + 2 from by ring, show 0 + 1 = 1 from by ring,
      show 3 * K + 3 = 0 + (3 * K + 3) from by ring]
  apply stepStar_trans (r3_chain (3 * K + 3) (a + 2) 0 1)
  rw [show a + 2 + (3 * K + 3) = a + 3 * K + 5 from by ring,
      show 1 + (3 * K + 3) = 0 + (3 * K + 4) from by ring]
  apply stepStar_trans (e_to_d (3 * K + 4) (a + 3 * K + 5) 0 0)
  rw [show 0 + (3 * K + 4) = 1 + 3 * (K + 1) from by ring,
      show a + 3 * K + 5 = (a + 2 * K + 4) + (K + 1) from by ring]
  apply stepStar_trans (drain_rounds (K + 1) (a + 2 * K + 4) 0 1)
  rw [show 0 + 5 * (K + 1) = 5 * K + 5 from by ring,
      show a + 2 * K + 4 = (a + 2 * K + 3) + 1 from by ring]
  apply stepStar_trans (base_d1 (a + 2 * K + 3) (5 * K + 5))
  rw [show 5 * K + 5 + 1 = 0 + (5 * K + 6) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (5 * K + 6) (a + 2 * K + 3) 0 1)
  ring_nf; finish

theorem trans_r0 : ⟨a + 1, 0, 3 * (K + 1), 0, 0⟩ [fm]⊢⁺ ⟨a + 7 * K + 6, 0, 5 * K + 7, 0, 0⟩ := by
  rw [show 3 * (K + 1) = (3 * K + 2) + 1 from by ring]
  apply step_stepStar_stepPlus (r3_first_step (a := a + 1) (c := 3 * K + 2) (e := 0))
  rw [show a + 1 + 1 = a + 2 from by ring, show 0 + 1 = 1 from by ring,
      show 3 * K + 2 = 0 + (3 * K + 2) from by ring]
  apply stepStar_trans (r3_chain (3 * K + 2) (a + 2) 0 1)
  rw [show a + 2 + (3 * K + 2) = a + 3 * K + 4 from by ring,
      show 1 + (3 * K + 2) = 0 + (3 * K + 3) from by ring]
  apply stepStar_trans (e_to_d (3 * K + 3) (a + 3 * K + 4) 0 0)
  rw [show 0 + (3 * K + 3) = 0 + 3 * (K + 1) from by ring,
      show a + 3 * K + 4 = (a + 2 * K + 3) + (K + 1) from by ring]
  apply stepStar_trans (drain_rounds (K + 1) (a + 2 * K + 3) 0 0)
  rw [show 0 + 5 * (K + 1) = (5 * K + 4) + 1 from by ring,
      show a + 2 * K + 3 = (a + 2 * K + 2) + 1 from by ring]
  apply stepStar_trans (base_d0 (a + 2 * K + 2) (5 * K + 4))
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 5 * K + 4 = 0 + (5 * K + 4) from by ring]
  apply stepStar_trans (r3r2_chain (5 * K + 4) (a + 2 * K + 2) 0 2)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 4, 0, 0⟩) (by execute fm 14)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c, 0, 0⟩ ∧ a ≥ 1 ∧ c ≥ 2)
  · intro q ⟨a, c, hq, ha, hc⟩; subst hq
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    obtain ⟨K, rfl | rfl | rfl⟩ : ∃ K, c = 3 * K ∨ c = 3 * K + 1 ∨ c = 3 * K + 2 := ⟨c / 3, by omega⟩
    · obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      exact ⟨⟨m + 7 * K + 6, 0, 5 * K + 7, 0, 0⟩,
        ⟨m + 7 * K + 6, 5 * K + 7, rfl, by omega, by omega⟩, trans_r0⟩
    · obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      exact ⟨⟨m + 7 * K + 9, 0, 5 * K + 8, 0, 0⟩,
        ⟨m + 7 * K + 9, 5 * K + 8, rfl, by omega, by omega⟩, trans_r1⟩
    · exact ⟨⟨m + 7 * K + 5, 0, 5 * K + 4, 0, 0⟩,
        ⟨m + 7 * K + 5, 5 * K + 4, rfl, by omega, by omega⟩, trans_r2⟩
  · exact ⟨3, 4, rfl, by omega, by omega⟩
