import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1949: [9/70, 55/2, 4/21, 7/11, 4/5]

Vector representation:
```
-1  2 -1 -1  0
-1  0  1  0  1
 2 -1  0 -1  0
 0  0  0  1 -1
 2  0 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1949

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k, ∀ d, ⟨(0 : ℕ), 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  step fm
  apply stepStar_trans (ih (d + 1)); ring_nf; finish

theorem r1r1r3_chain : ∀ k, ∀ b, ⟨2, b, c + 2 * k, d + 3 * k, (0 : ℕ)⟩ [fm]⊢*
    ⟨2, b + 3 * k, c, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
      show d + 3 * (k + 1) = (d + 3 * k) + 1 + 1 + 1 from by ring]
  step fm; step fm
  rw [show b + 2 + 2 = (b + 3) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (b + 3)); rw [show b + 3 + 3 * k = b + 3 * (k + 1) from by ring]; finish

theorem spiral : ∀ k, ∀ b, ⟨(0 : ℕ), b + k, c, 0, e + 1⟩ [fm]⊢*
    ⟨0, b, c + 2 * k, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  rw [show b + (k + 1) = (b + 1) + k from by ring]
  apply stepStar_trans (ih (b + 1))
  rw [show e + k + 1 = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (step_stepStar
    (show ⟨2, b, c + 2 * k, (0 : ℕ), e + k⟩ [fm]⊢ ⟨1, b, c + 2 * k + 1, 0, e + k + 1⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar
    (show ⟨1, b, c + 2 * k + 1, (0 : ℕ), e + k + 1⟩ [fm]⊢ ⟨0, b, c + 2 * k + 2, 0, e + k + 2⟩ from by simp [fm]))
  rw [show c + 2 * (k + 1) = c + 2 * k + 2 from by ring,
      show e + (k + 1) + 1 = e + k + 2 from by ring]; finish

-- R5 step helper
theorem r5_step (c d : ℕ) : ⟨(0 : ℕ), 0, c + 1, d, 0⟩ [fm]⊢ ⟨2, 0, c, d, 0⟩ := by simp [fm]

-- R2 step helpers
theorem r2_step_2 (b c : ℕ) : ⟨2, b, c, (0 : ℕ), 0⟩ [fm]⊢ ⟨1, b, c + 1, 0, 1⟩ := by simp [fm]
theorem r2_step_1 (b c e : ℕ) : ⟨1, b, c, (0 : ℕ), e⟩ [fm]⊢ ⟨0, b, c + 1, 0, e + 1⟩ := by simp [fm]

-- R5 for symbolic b: (0, b, c+1, 0, 0) -> (2, b, c, 0, 0)
theorem r5_step' (b c : ℕ) : ⟨(0 : ℕ), b, c + 1, 0, 0⟩ [fm]⊢ ⟨2, b, c, 0, 0⟩ := by simp [fm]

theorem main_trans_mod0 :
    ⟨(0 : ℕ), 0, F + 2 * k + 3, 0, 3 * k + 3⟩ [fm]⊢⁺
    ⟨0, 0, F + 6 * k + 8, 0, 3 * k + 5⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_d (3 * k + 3) 0 (c := F + 2 * k + 3))
  rw [show 0 + (3 * k + 3) = 3 * k + 3 from by ring]
  rw [show F + 2 * k + 3 = (F + 2 * k + 2) + 1 from by ring]
  apply step_stepStar_stepPlus (r5_step (F + 2 * k + 2) (3 * k + 3))
  rw [show F + 2 * k + 2 = F + 2 * (k + 1) from by ring,
      show 3 * k + 3 = 0 + 3 * (k + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (k + 1) 0)
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
  apply stepStar_trans (step_stepStar (r2_step_2 (3 * k + 3) F))
  apply stepStar_trans (step_stepStar (r2_step_1 (3 * k + 3) (F + 1) 1))
  rw [show F + 1 + 1 = F + 2 from by ring,
      show 3 * k + 3 = 0 + (3 * k + 3) from by ring,
      show (1 + 1 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (spiral (3 * k + 3) 0 (c := F + 2) (e := 1))
  rw [show F + 2 + 2 * (3 * k + 3) = F + 6 * k + 8 from by ring,
      show 1 + (3 * k + 3) + 1 = 3 * k + 5 from by ring]; finish

theorem main_trans_mod1 :
    ⟨(0 : ℕ), 0, F + 2 * k + 4, 0, 3 * k + 4⟩ [fm]⊢⁺
    ⟨0, 0, F + 6 * k + 11, 0, 3 * k + 6⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_d (3 * k + 4) 0 (c := F + 2 * k + 4))
  rw [show 0 + (3 * k + 4) = 3 * k + 4 from by ring]
  rw [show F + 2 * k + 4 = (F + 2 * k + 3) + 1 from by ring]
  apply step_stepStar_stepPlus (r5_step (F + 2 * k + 3) (3 * k + 4))
  rw [show F + 2 * k + 3 = (F + 1) + 2 * (k + 1) from by ring,
      show 3 * k + 4 = 1 + 3 * (k + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (k + 1) 0 (c := F + 1) (d := 1))
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring,
      show F + 1 = F + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (3 * k + 3) + 2 = 3 * k + 5 from by ring]
  apply stepStar_trans (step_stepStar (r2_step_1 (3 * k + 5) F 0))
  rw [show 3 * k + 5 = 0 + (3 * k + 5) from by ring,
      show (0 + 1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (spiral (3 * k + 5) 0 (c := F + 1) (e := 0))
  rw [show F + 1 + 2 * (3 * k + 5) = F + 6 * k + 11 from by ring,
      show 0 + (3 * k + 5) + 1 = 3 * k + 6 from by ring]; finish

theorem main_trans_mod2 :
    ⟨(0 : ℕ), 0, F + 2 * k + 6, 0, 3 * k + 5⟩ [fm]⊢⁺
    ⟨0, 0, F + 6 * k + 16, 0, 3 * k + 9⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_d (3 * k + 5) 0 (c := F + 2 * k + 6))
  rw [show 0 + (3 * k + 5) = 3 * k + 5 from by ring]
  rw [show F + 2 * k + 6 = (F + 2 * k + 5) + 1 from by ring]
  apply step_stepStar_stepPlus (r5_step (F + 2 * k + 5) (3 * k + 5))
  rw [show F + 2 * k + 5 = (F + 3) + 2 * (k + 1) from by ring,
      show 3 * k + 5 = 2 + 3 * (k + 1) from by ring]
  apply stepStar_trans (r1r1r3_chain (k + 1) 0 (c := F + 3) (d := 2))
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring,
      show F + 3 = (F + 2) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (3 * k + 3) + 2 = (3 * k + 4) + 1 from by ring,
      show F + 2 = (F + 1) + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (3 * k + 4 + 1) + 2 = 3 * k + 7 from by ring,
      show F + 1 = F + 1 from by ring]
  apply stepStar_trans (step_stepStar (r5_step' (3 * k + 7) F))
  apply stepStar_trans (step_stepStar (r2_step_2 (3 * k + 7) F))
  apply stepStar_trans (step_stepStar (r2_step_1 (3 * k + 7) (F + 1) 1))
  rw [show F + 1 + 1 = F + 2 from by ring,
      show 3 * k + 7 = 0 + (3 * k + 7) from by ring,
      show (1 + 1 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (spiral (3 * k + 7) 0 (c := F + 2) (e := 1))
  rw [show F + 2 + 2 * (3 * k + 7) = F + 6 * k + 16 from by ring,
      show 1 + (3 * k + 7) + 1 = 3 * k + 9 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 3⟩) (by execute fm 13)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ c ≥ e + 1 ∧ e ≥ 3)
  · intro q ⟨c, e, hq, hc, he⟩; subst hq
    rcases (show e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 from by omega) with h | h | h
    · obtain ⟨K, hK⟩ : ∃ K, e = 3 * K := ⟨e / 3, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩; rw [hK]
      obtain ⟨F, rfl⟩ : ∃ F, c = F + 2 * k + 3 := ⟨c - 2 * k - 3, by omega⟩
      exact ⟨_, ⟨F + 6 * k + 8, 3 * k + 5, rfl, by omega, by omega⟩, main_trans_mod0⟩
    · obtain ⟨K, hK⟩ : ∃ K, e = 3 * K + 1 := ⟨e / 3, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩; rw [hK]
      obtain ⟨F, rfl⟩ : ∃ F, c = F + 2 * k + 4 := ⟨c - 2 * k - 4, by omega⟩
      exact ⟨_, ⟨F + 6 * k + 11, 3 * k + 6, rfl, by omega, by omega⟩, main_trans_mod1⟩
    · obtain ⟨K, hK⟩ : ∃ K, e = 3 * K + 2 := ⟨e / 3, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩; rw [hK]
      obtain ⟨F, rfl⟩ : ∃ F, c = F + 2 * k + 6 := ⟨c - 2 * k - 6, by omega⟩
      exact ⟨_, ⟨F + 6 * k + 16, 3 * k + 9, rfl, by omega, by omega⟩, main_trans_mod2⟩
  · exact ⟨4, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1949
