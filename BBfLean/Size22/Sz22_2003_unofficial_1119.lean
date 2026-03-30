import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1119: [5/6, 4/35, 847/2, 9/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  1  2
 0  2  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1119

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3 repeated: drain a to d and e.
theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1) (e + 2))
    ring_nf; finish

-- R4 repeated: drain d to b.
theorem r4_drain : ∀ k, ∀ b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 2) e)
    ring_nf; finish

-- R3 drain + R4 drain + R5,R1,R2 bootstrap.
theorem drain_and_bootstrap :
    ⟨a + 2, 0, 0, 0, e⟩ [fm]⊢* ⟨2, 2 * a + 3, 0, 0, e + 2 * a + 3⟩ := by
  apply stepStar_trans (r3_drain (a + 2) 0 e)
  rw [show 0 + (a + 2) = a + 2 from by ring]
  apply stepStar_trans (r4_drain (a + 2) 0 (e + 2 * (a + 2)))
  rw [show 0 + 2 * (a + 2) = 2 * a + 3 + 1 from by ring,
      show e + 2 * (a + 2) = e + 2 * a + 3 + 1 from by ring]
  step fm; step fm; step fm; finish

-- 5-step cycle: R1,R1,R5,R1,R2.
theorem five_step : ∀ b C, ⟨2, b + 3, C, 0, e + 1⟩ [fm]⊢* ⟨2, b, C + 2, 0, e⟩ := by
  intro b C; step fm; step fm; step fm; step fm; step fm; finish

-- Spiral-down loop, remainder 0.
theorem fsl_r0 : ∀ k, ∀ C,
    ⟨2, 3 * k, C, 0, e + k⟩ [fm]⊢* ⟨2, 0, C + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro C
  · exists 0
  · rw [show 3 * (k + 1) = 3 * k + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans (five_step (3 * k) C (e := e + k))
    apply stepStar_trans (ih (C + 2)); ring_nf; finish

-- Spiral-down loop, remainder 1.
theorem fsl_r1 : ∀ k, ∀ C,
    ⟨2, 3 * k + 1, C, 0, e + k⟩ [fm]⊢* ⟨2, 1, C + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro C
  · exists 0
  · rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans (five_step (3 * k + 1) C (e := e + k))
    apply stepStar_trans (ih (C + 2)); ring_nf; finish

-- Spiral-down loop, remainder 2.
theorem fsl_r2 : ∀ k, ∀ C,
    ⟨2, 3 * k + 2, C, 0, e + k⟩ [fm]⊢* ⟨2, 2, C + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro C
  · exists 0
  · rw [show 3 * (k + 1) + 2 = 3 * k + 2 + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans (five_step (3 * k + 2) C (e := e + k))
    apply stepStar_trans (ih (C + 2)); ring_nf; finish

-- R3,R2 spiral-up chain.
theorem r32_chain : ∀ k, ∀ A c E,
    ⟨A + 1, 0, c + k, 0, E⟩ [fm]⊢* ⟨A + k + 1, 0, c, 0, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A c E
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (A + 1) c (E + 2))
    ring_nf; finish

-- a = 3m+2: spiral-down remainder 0, then R3,R2 spiral-up.
theorem trans_mod2 : ∀ m e,
    ⟨3 * m + 2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨4 * m + 4, 0, 0, 0, e + 12 * m + 6⟩ := by
  intro m e
  apply stepStar_stepPlus_stepPlus drain_and_bootstrap
  show ⟨2, 2 * (3 * m) + 3, 0, 0, e + 2 * (3 * m) + 3⟩ [fm]⊢⁺ _
  rw [show 2 * (3 * m) + 3 = 3 * (2 * m + 1) from by ring,
      show e + 2 * (3 * m) + 3 = (e + 4 * m + 2) + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (fsl_r0 (2 * m + 1) 0 (e := e + 4 * m + 2))
  rw [show 0 + 2 * (2 * m + 1) = 0 + (4 * m + 2) from by ring]
  step fm; step fm
  rw [show e + 4 * m + 2 + 2 = e + 4 * m + 4 from by ring]
  apply stepStar_trans (r32_chain (4 * m + 1) 2 0 (e + 4 * m + 4))
  ring_nf; finish

-- a = 3m+3: spiral-down remainder 2, then R1,R1,R5,R2, then R3,R2 spiral-up.
theorem trans_mod0 : ∀ m e,
    ⟨3 * m + 3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨4 * m + 6, 0, 0, 0, e + 12 * m + 9⟩ := by
  intro m e
  apply stepStar_stepPlus_stepPlus drain_and_bootstrap
  show ⟨2, 2 * (3 * m + 1) + 3, 0, 0, e + 2 * (3 * m + 1) + 3⟩ [fm]⊢⁺ _
  rw [show 2 * (3 * m + 1) + 3 = 3 * (2 * m + 1) + 2 from by ring,
      show e + 2 * (3 * m + 1) + 3 = (e + 4 * m + 4) + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (fsl_r2 (2 * m + 1) 0 (e := e + 4 * m + 4))
  rw [show 0 + 2 * (2 * m + 1) = 4 * m + 2 from by ring]
  rw [show e + 4 * m + 4 = (e + 4 * m + 3) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 4 * m + 3 = 0 + (4 * m + 3) from by ring]
  apply stepStar_trans (r32_chain (4 * m + 3) 2 0 (e + 4 * m + 3))
  ring_nf; finish

-- a = 3m+4: spiral-down remainder 1, then R1, then R3,R2 spiral-up.
theorem trans_mod1 : ∀ m e,
    ⟨3 * m + 4, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨4 * m + 6, 0, 0, 0, e + 12 * m + 15⟩ := by
  intro m e
  apply stepStar_stepPlus_stepPlus drain_and_bootstrap
  show ⟨2, 2 * (3 * m + 2) + 3, 0, 0, e + 2 * (3 * m + 2) + 3⟩ [fm]⊢⁺ _
  rw [show 2 * (3 * m + 2) + 3 = 3 * (2 * m + 2) + 1 from by ring,
      show e + 2 * (3 * m + 2) + 3 = (e + 4 * m + 5) + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (fsl_r1 (2 * m + 2) 0 (e := e + 4 * m + 5))
  rw [show 0 + 2 * (2 * m + 2) = 4 * m + 4 from by ring]
  step fm
  rw [show 4 * m + 4 + 1 = 0 + (4 * m + 5) from by ring]
  apply stepStar_trans (r32_chain (4 * m + 5) 0 0 (e + 4 * m + 5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 2)
  · intro c ⟨a, e, hq, ha⟩; subst hq
    rcases (show a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 from by omega) with h | h | h
    · obtain ⟨m, rfl⟩ : ∃ m, a = 3 * m + 3 := ⟨a / 3 - 1, by omega⟩
      exact ⟨⟨4 * m + 6, 0, 0, 0, e + 12 * m + 9⟩,
        ⟨4 * m + 6, e + 12 * m + 9, rfl, by omega⟩, trans_mod0 m e⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = 3 * m + 4 := ⟨a / 3 - 1, by omega⟩
      exact ⟨⟨4 * m + 6, 0, 0, 0, e + 12 * m + 15⟩,
        ⟨4 * m + 6, e + 12 * m + 15, rfl, by omega⟩, trans_mod1 m e⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = 3 * m + 2 := ⟨a / 3, by omega⟩
      exact ⟨⟨4 * m + 4, 0, 0, 0, e + 12 * m + 6⟩,
        ⟨4 * m + 4, e + 12 * m + 6, rfl, by omega⟩, trans_mod2 m e⟩
  · exact ⟨2, 3, rfl, by omega⟩

end Sz22_2003_unofficial_1119
