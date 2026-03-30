import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1108: [5/6, 4/35, 539/2, 3/49, 14/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  1
 0  1  0 -2  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1108

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

theorem r4_drain : ∀ k, ∀ b e, ⟨0, b, 0, 2 * k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

theorem r4_drain_odd : ∀ k, ∀ b e,
    ⟨0, b, 0, 2 * k + 1, e⟩ [fm]⊢* ⟨0, b + k, 0, 1, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

theorem r322_even : ∀ k, ∀ a e,
    ⟨a + 1, 0, 2 * k, 0, e⟩ [fm]⊢* ⟨a + 1 + 3 * k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (e + 1))
    ring_nf; finish

theorem r322_odd_tail : ∀ k, ∀ a e,
    ⟨a + 1, 0, 2 * k + 1, 0, e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, 3, e + k + 2⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (e + 1))
    ring_nf; finish

theorem five_step : ∀ b C, ⟨2, b + 3, C, 0, e + 1⟩ [fm]⊢* ⟨2, b, C + 2, 0, e⟩ := by
  intro b C; step fm; step fm; step fm; step fm; step fm; finish

theorem fsl_r0 : ∀ k, ∀ C,
    ⟨2, 3 * k, C, 0, e + k⟩ [fm]⊢* ⟨2, 0, C + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro C
  · exists 0
  · rw [show 3 * (k + 1) = 3 * k + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans (five_step (3 * k) C (e := e + k))
    apply stepStar_trans (ih (C + 2)); ring_nf; finish

theorem fsl_r1 : ∀ k, ∀ C,
    ⟨2, 3 * k + 1, C, 0, e + k⟩ [fm]⊢* ⟨2, 1, C + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro C
  · exists 0
  · rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans (five_step (3 * k + 1) C (e := e + k))
    apply stepStar_trans (ih (C + 2)); ring_nf; finish

theorem fsl_r2 : ∀ k, ∀ C,
    ⟨2, 3 * k + 2, C, 0, e + k⟩ [fm]⊢* ⟨2, 2, C + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro C
  · exists 0
  · rw [show 3 * (k + 1) + 2 = 3 * k + 2 + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    apply stepStar_trans (five_step (3 * k + 2) C (e := e + k))
    apply stepStar_trans (ih (C + 2)); ring_nf; finish

theorem drain_and_bootstrap :
    ⟨a + 2, 0, 0, 0, e⟩ [fm]⊢* ⟨2, a + 1, 0, 0, e + a + 1⟩ := by
  apply stepStar_trans (r3_drain (a + 2) 0 e)
  rw [show 0 + 2 * (a + 2) = 2 * (a + 2) from by ring]
  apply stepStar_trans (r4_drain (a + 2) 0 (e + (a + 2)))
  rw [show 0 + (a + 2) = a + 1 + 1 from by ring,
      show e + (a + 2) = e + a + 1 + 1 from by ring]
  step fm; step fm; step fm; finish

-- Second drain: (A+1, 0, 0, 3, G) →* (2, A+1, 0, 1, G+A).
theorem second_drain_to_21 : ∀ A G,
    ⟨A + 1, 0, 0, 3, G⟩ [fm]⊢* ⟨2, A + 1, 0, 1, G + A⟩ := by
  intro A G
  apply stepStar_trans (r3_drain (A + 1) 3 G)
  rw [show 3 + 2 * (A + 1) = 2 * (A + 2) + 1 from by ring]
  apply stepStar_trans (r4_drain_odd (A + 2) 0 (G + (A + 1)))
  rw [show 0 + (A + 2) = A + 2 from by ring,
      show G + (A + 1) = G + A + 1 from by ring]
  step fm; step fm; step fm
  ring_nf; finish

-- Cleanup: (2, B+2, 0, 1, F) →* (2, B, 1, 0, F).
theorem cleanup_r1r1r2 : ⟨2, B + 2, 0, 1, F⟩ [fm]⊢* ⟨2, B, 1, 0, F⟩ := by
  step fm; step fm; step fm; finish

-- Main transition for a ≡ 1 (mod 3): a = 3m+4, m >= 0.
theorem trans_mod1 : ∀ m e,
    ⟨3 * m + 4, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * m + 5, 0, 0, 0, e + 3 * m + 3⟩ := by
  intro m e
  -- drain_and_bootstrap: ⊢* to (2, 3m+3, 0, 0, e+3m+3).
  -- fsl_r0: ⊢* to (2, 0, 2(m+1), 0, e+2m+2).
  -- R3R2R2 chain: ⊢* to (3m+5, 0, 0, 0, e+3m+3). Gives ⊢⁺ since at least 3 steps.
  apply stepStar_stepPlus_stepPlus drain_and_bootstrap
  show ⟨2, 3 * (m + 1), 0, 0, e + 3 * m + 3⟩ [fm]⊢⁺ _
  rw [show e + 3 * m + 3 = (e + 2 * m + 2) + (m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (fsl_r0 (m + 1) 0 (e := e + 2 * m + 2))
  rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring]
  -- (2, 0, 2m+2, 0, e+2m+2). R3,R2,R2 + r322_even m.
  step fm; step fm; step fm
  show ⟨5, 0, 2 * m, 0, e + 2 * m + 3⟩ [fm]⊢* _
  apply stepStar_trans (r322_even m 4 (e + 2 * m + 3))
  ring_nf; finish

-- Main transition for a = 2: (2, 0, 0, 0, e) →⁺ (3, 0, 0, 0, e+3).
theorem trans_a2 : ∀ e,
    ⟨2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3, 0, 0, 0, e + 3⟩ := by
  intro e
  apply stepStar_stepPlus_stepPlus drain_and_bootstrap
  execute fm 12

-- Main transition for a ≡ 2 (mod 3), a >= 5: a = 3(m+1)+2, m >= 0.
-- (3m+5, 0, 0, 0, e) →⁺ (3m+6, 0, 0, 0, e+6m+9).
theorem trans_mod2 : ∀ m e,
    ⟨3 * (m + 1) + 2, 0, 0, 0, e⟩ [fm]⊢⁺
    ⟨3 * (m + 1) + 3, 0, 0, 0, e + 6 * (m + 1) + 3⟩ := by
  intro m e
  apply stepStar_stepPlus_stepPlus drain_and_bootstrap
  -- (2, 3m+4, 0, 0, e+3m+4). b = 3(m+1)+1.
  show ⟨2, 3 * (m + 1) + 1, 0, 0, e + 3 * (m + 1) + 1⟩ [fm]⊢⁺ _
  rw [show e + 3 * (m + 1) + 1 = (e + 2 * m + 3) + (m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (fsl_r1 (m + 1) 0 (e := e + 2 * m + 3))
  rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring]
  -- (2, 1, 2m+2, 0, e+2m+3). R1.
  step fm
  -- (1, 0, 2m+3, 0, e+2m+3). r322_odd_tail (m+1) with a=0.
  show ⟨1, 0, 2 * (m + 1) + 1, 0, e + 2 * m + 3⟩ [fm]⊢* _
  rw [show e + 2 * m + 3 = e + 2 * (m + 1) + 1 from by ring]
  apply stepStar_trans (r322_odd_tail (m + 1) 0 (e + 2 * (m + 1) + 1))
  rw [show 0 + 3 * (m + 1) + 1 = 3 * m + 4 from by ring,
      show e + 2 * (m + 1) + 1 + (m + 1) + 2 = e + 3 * m + 6 from by ring]
  -- (3m+4, 0, 0, 3, e+3m+6). second_drain_to_21 (3m+3).
  apply stepStar_trans (second_drain_to_21 (3 * m + 3) (e + 3 * m + 6))
  rw [show e + 3 * m + 6 + (3 * m + 3) = e + 6 * m + 9 from by ring]
  -- (2, 3m+4, 0, 1, e+6m+9). cleanup: R1,R1,R2 -> (2, 3m+2, 1, 0, e+6m+9).
  rw [show 3 * m + 3 + 1 = 3 * m + 2 + 2 from by ring]
  apply stepStar_trans cleanup_r1r1r2
  -- (2, 3m+2, 1, 0, e+6m+9). fsl_r2 m with C=1.
  rw [show e + 6 * m + 9 = (e + 5 * m + 9) + m from by ring]
  apply stepStar_trans (fsl_r2 m 1 (e := e + 5 * m + 9))
  rw [show 1 + 2 * m = 2 * m + 1 from by ring]
  -- (2, 2, 2m+1, 0, e+5m+9). R1,R1.
  step fm; step fm
  -- (0, 0, 2m+3, 0, e+5m+9). R5,R2.
  show ⟨0, 0, 2 * m + 3, 0, e + 5 * m + 9⟩ [fm]⊢* _
  rw [show e + 5 * m + 9 = e + 5 * m + 8 + 1 from by ring]
  step fm; step fm
  -- (3, 0, 2m+2, 0, e+5m+8). R3,R2,R2 + r322_even m.
  show ⟨3, 0, 2 * m + 2, 0, e + 5 * m + 8⟩ [fm]⊢* _
  rw [show 2 * m + 2 = 2 * m + 2 from rfl]
  step fm; step fm; step fm
  show ⟨6, 0, 2 * m, 0, e + 5 * m + 9⟩ [fm]⊢* _
  apply stepStar_trans (r322_even m 5 (e + 5 * m + 9))
  ring_nf; finish

-- Main transition for a ≡ 0 (mod 3): a = 3m+3, m >= 0.
-- (3m+3, 0, 0, 0, e) →⁺ (3m+4, 0, 0, 0, e+6m+6).
theorem trans_mod0 : ∀ m e,
    ⟨3 * m + 3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨3 * m + 4, 0, 0, 0, e + 6 * m + 6⟩ := by
  intro m e
  apply stepStar_stepPlus_stepPlus drain_and_bootstrap
  -- (2, 3m+2, 0, 0, e+3m+2).
  show ⟨2, 3 * m + 2, 0, 0, e + 3 * m + 2⟩ [fm]⊢⁺ _
  rw [show e + 3 * m + 2 = (e + 2 * m + 2) + m from by ring]
  apply stepStar_stepPlus_stepPlus (fsl_r2 m 0 (e := e + 2 * m + 2))
  rw [show 0 + 2 * m = 2 * m from by ring]
  -- (2, 2, 2m, 0, e+2m+2). R1,R1.
  step fm; step fm
  -- (0, 0, 2m+2, 0, e+2m+2). R5,R2.
  show ⟨0, 0, 2 * m + 2, 0, e + 2 * m + 2⟩ [fm]⊢* _
  rw [show e + 2 * m + 2 = e + 2 * m + 1 + 1 from by ring]
  step fm; step fm
  -- (3, 0, 2m+1, 0, e+2m+1). r322_odd_tail m with a=2.
  show ⟨3, 0, 2 * m + 1, 0, e + 2 * m + 1⟩ [fm]⊢* _
  apply stepStar_trans (r322_odd_tail m 2 (e + 2 * m + 1))
  rw [show 2 + 3 * m + 1 = 3 * m + 3 from by ring,
      show e + 2 * m + 1 + m + 2 = e + 3 * m + 3 from by ring]
  -- (3m+3, 0, 0, 3, e+3m+3). second_drain_to_21 (3m+2).
  apply stepStar_trans (second_drain_to_21 (3 * m + 2) (e + 3 * m + 3))
  rw [show e + 3 * m + 3 + (3 * m + 2) = e + 6 * m + 5 from by ring]
  -- (2, 3m+3, 0, 1, e+6m+5). cleanup: R1,R1,R2 -> (2, 3m+1, 1, 0, e+6m+5).
  rw [show 3 * m + 2 + 1 = 3 * m + 1 + 2 from by ring]
  apply stepStar_trans cleanup_r1r1r2
  -- (2, 3m+1, 1, 0, e+6m+5). fsl_r1 m with C=1.
  rw [show e + 6 * m + 5 = (e + 5 * m + 5) + m from by ring]
  apply stepStar_trans (fsl_r1 m 1 (e := e + 5 * m + 5))
  rw [show 1 + 2 * m = 2 * m + 1 from by ring]
  -- (2, 1, 2m+1, 0, e+5m+5). R1.
  step fm
  -- (1, 0, 2m+2, 0, e+5m+5). r322_even (m+1) with a=0.
  show ⟨1, 0, 2 * m + 2, 0, e + 5 * m + 5⟩ [fm]⊢* _
  rw [show 2 * m + 2 = 2 * (m + 1) from by ring]
  apply stepStar_trans (r322_even (m + 1) 0 (e + 5 * m + 5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 2)
  · intro c ⟨a, e, hq, ha⟩; subst hq
    rcases (show a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 from by omega) with h | h | h
    · -- a ≡ 0 mod 3: a = 3m+3 with m >= 0
      obtain ⟨m, rfl⟩ : ∃ m, a = 3 * m + 3 := ⟨a / 3 - 1, by omega⟩
      exact ⟨⟨3 * m + 4, 0, 0, 0, e + 6 * m + 6⟩,
        ⟨3 * m + 4, e + 6 * m + 6, rfl, by omega⟩, trans_mod0 m e⟩
    · -- a ≡ 1 mod 3: if a >= 4 then a = 3m+4, else impossible (a ≡ 1 mod 3 and a >= 2 means a >= 4)
      obtain ⟨m, rfl⟩ : ∃ m, a = 3 * m + 4 := ⟨a / 3 - 1, by omega⟩
      exact ⟨⟨3 * m + 5, 0, 0, 0, e + 3 * m + 3⟩,
        ⟨3 * m + 5, e + 3 * m + 3, rfl, by omega⟩, trans_mod1 m e⟩
    · -- a ≡ 2 mod 3: a = 2 or a = 3m+5 with m >= 0
      rcases (show a = 2 ∨ a ≥ 5 from by omega) with rfl | h'
      · exact ⟨⟨3, 0, 0, 0, e + 3⟩,
          ⟨3, e + 3, rfl, by omega⟩, trans_a2 e⟩
      · obtain ⟨m, rfl⟩ : ∃ m, a = 3 * (m + 1) + 2 := ⟨a / 3 - 1, by omega⟩
        exact ⟨⟨3 * (m + 1) + 3, 0, 0, 0, e + 6 * (m + 1) + 3⟩,
          ⟨3 * (m + 1) + 3, e + 6 * (m + 1) + 3, rfl, by omega⟩, trans_mod2 m e⟩
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1108
