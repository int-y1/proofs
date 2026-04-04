import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1799: [9/10, 539/2, 2/21, 5/7, 28/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  2  1
 1 -1  0 -1  0
 0  0  1 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1799

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

theorem d_to_c : ∀ k, ∀ c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  rw [Nat.add_succ d k]; step fm
  apply stepStar_trans (ih (c + 1) d)
  ring_nf; finish

theorem main_loop : ∀ n, ∀ b c e, ⟨0, b, c + 3 * n, 0, e + n⟩ [fm]⊢* ⟨0, b + 5 * n, c, 0, e⟩ := by
  intro n; induction' n with n ih <;> intro b c e
  · exists 0
  rw [show c + 3 * (n + 1) = (c + 3 * n) + 3 from by ring,
      show e + (n + 1) = (e + n) + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (ih (b + 5) c e)
  ring_nf; finish

theorem drain : ∀ k, ∀ d e, ⟨0, k + 1, 0, d + 1, e⟩ [fm]⊢* ⟨1, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · step fm; finish
  rw [show (k + 1) + 1 = k + 1 + 1 from rfl]
  step fm; step fm
  apply stepStar_trans (ih (d + 1) (e + 1))
  ring_nf; finish

theorem exit_r0 : ⟨0, b + 2, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨1, 0, 0, b + 5, e + b + 3⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (drain b 5 (e + 3))
  ring_nf; finish

theorem exit_r1 : ⟨0, b, 1, 0, e + 1⟩ [fm]⊢⁺ ⟨1, 0, 0, b + 3, e + b + 2⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (drain b 3 (e + 2))
  ring_nf; finish

theorem exit_r2 : ⟨0, b, 2, 0, e + 1⟩ [fm]⊢⁺ ⟨1, 0, 0, b + 3, e + b + 3⟩ := by
  step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (drain (b + 2) 1 (e + 1))
  ring_nf; finish

-- d=3(n+1): (0,0,0,3(n+1),e) →⁺ (0,0,0,5n+10,e+4n+5)
-- Requires e ≥ n+2 so main loop and exit have enough fuel.
theorem trans_r0 (n : ℕ) (he : e ≥ n + 2) :
    ⟨0, 0, 0, 3 * (n + 1), e⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * n + 10, e + 4 * n + 5⟩ := by
  obtain ⟨F, rfl⟩ : ∃ F, e = F + n + 2 := ⟨e - n - 2, by omega⟩
  rw [show 3 * (n + 1) = 0 + 3 * (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (3 * (n + 1)) 0 0)
  simp only [Nat.zero_add]
  rw [show 3 * (n + 1) = 0 + 3 * (n + 1) from by ring,
      show F + n + 2 = (F + 1) + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (main_loop (n + 1) 0 0 (F + 1))
  simp only [Nat.zero_add]
  rw [show 5 * (n + 1) = (5 * n + 3) + 2 from by ring,
      show F + 1 = F + 1 from rfl]
  apply stepPlus_stepStar_stepPlus (exit_r0 (b := 5 * n + 3) (e := F))
  step fm
  ring_nf; finish

-- d=3(n+1)+1
theorem trans_r1 (n : ℕ) (he : e ≥ n + 2) :
    ⟨0, 0, 0, 3 * (n + 1) + 1, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * n + 10, e + 4 * n + 6⟩ := by
  obtain ⟨F, rfl⟩ : ∃ F, e = F + n + 2 := ⟨e - n - 2, by omega⟩
  rw [show 3 * (n + 1) + 1 = 0 + (3 * (n + 1) + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (3 * (n + 1) + 1) 0 0)
  simp only [Nat.zero_add]
  rw [show 3 * (n + 1) + 1 = 1 + 3 * (n + 1) from by ring,
      show F + n + 2 = (F + 1) + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (main_loop (n + 1) 0 1 (F + 1))
  simp only [Nat.zero_add]
  rw [show F + 1 = F + 1 from rfl]
  apply stepPlus_stepStar_stepPlus (exit_r1 (b := 5 * (n + 1)) (e := F))
  step fm
  ring_nf; finish

-- d=3n+2
theorem trans_r2 (n : ℕ) (he : e ≥ n + 1) :
    ⟨0, 0, 0, 3 * n + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 5 * n + 5, e + 4 * n + 3⟩ := by
  obtain ⟨F, rfl⟩ : ∃ F, e = F + n + 1 := ⟨e - n - 1, by omega⟩
  rw [show 3 * n + 2 = 0 + (3 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (3 * n + 2) 0 0)
  simp only [Nat.zero_add]
  rw [show 3 * n + 2 = 2 + 3 * n from by ring,
      show F + n + 1 = (F + 1) + n from by ring]
  apply stepStar_stepPlus_stepPlus (main_loop n 0 2 (F + 1))
  simp only [Nat.zero_add]
  rw [show F + 1 = F + 1 from rfl]
  apply stepPlus_stepStar_stepPlus (exit_r2 (b := 5 * n) (e := F))
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 2 ∧ 3 * e ≥ d + 1)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    obtain ⟨q, rfl | rfl | rfl⟩ : ∃ q, d = 3 * q ∨ d = 3 * q + 1 ∨ d = 3 * q + 2 :=
      ⟨d / 3, by omega⟩
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 5 * q' + 10, e + 4 * q' + 5⟩,
        ⟨5 * q' + 10, e + 4 * q' + 5, rfl, by omega, by omega⟩,
        trans_r0 q' (by omega)⟩
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 5 * q' + 10, e + 4 * q' + 6⟩,
        ⟨5 * q' + 10, e + 4 * q' + 6, rfl, by omega, by omega⟩,
        trans_r1 q' (by omega)⟩
    · exact ⟨⟨0, 0, 0, 5 * q + 5, e + 4 * q + 3⟩,
        ⟨5 * q + 5, e + 4 * q + 3, rfl, by omega, by omega⟩,
        trans_r2 q (by omega)⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩
