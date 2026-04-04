import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1834: [9/10, 77/2, 4/21, 5/7, 98/11]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  1  1
 2 -1  0 -1  0
 0  0  1 -1  0
 1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1834

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

theorem d_to_c : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (c := c + 1) (d := d)); ring_nf; finish

theorem open_spiral : ∀ k, ⟨0, 0, c + 5 * k + 1, 0, e + k + 1⟩ [fm]⊢*
    ⟨0, 2 + 8 * k, c, 2, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · step fm; step fm; finish
  · rw [show c + 5 * (k + 1) + 1 = (c + 5) + 5 * k + 1 from by ring,
        show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring]
    apply stepStar_trans (ih (c := c + 5) (e := e + 1))
    rw [show c + 5 = (c + 4) + 1 from by ring,
        show 2 + 8 * k = (1 + 8 * k) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show e + 1 = e + 0 + 1 from by ring]
    step fm; step fm
    rw [show (1 + 8 * k) + 0 + 2 = (3 + 8 * k) from by ring,
        show c + 4 = (c + 3) + 1 from by ring]
    step fm
    rw [show 3 + 8 * k + 2 = (4 + 8 * k) + 1 from by ring]
    step fm
    rw [show c + 3 = (c + 2) + 1 from by ring]
    step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show 2 + 8 * (k + 1) = 4 + 8 * k + 2 + 2 + 2 from by ring]; ring_nf; finish

theorem drain : ∀ B, ∀ d e, ⟨0, B + 1, 0, d + 1, e⟩ [fm]⊢* ⟨2, 0, 0, d + B, e + 2 * B⟩ := by
  intro B; induction' B with B ih <;> intro d e
  · step fm; finish
  · rw [show d + 1 = d + 0 + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 0 + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d + 1) (e + 2)); ring_nf; finish

-- r=3: (0, B+1, 3, 2, e) with B ≥ 0 → 9 tail steps then drain
-- Proved by: R3,R1,R1,R3,R1,R2,R3,R2,R2 then drain(B, 1, e+3)
theorem tail3_drain : ∀ B, ⟨0, B + 1, 3, 2, e⟩ [fm]⊢⁺
    ⟨2, 0, 0, B + 4, e + 2 * B + 9⟩ := by
  intro B
  rw [show (3 : ℕ) = 2 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show B + 0 + 2 + 2 = (B + 3) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm
  -- State: (1, B+5, 0, 0, e). R2 fires.
  apply stepStar_trans (step_stepStar (by simp [fm] :
    ⟨1, B + 3 + 2, 0, 0, e⟩ [fm]⊢ ⟨0, B + 3 + 2, 0, 1, e + 1⟩))
  rw [show B + 3 + 2 = (B + 4) + 1 from by ring]
  step fm
  apply stepStar_trans (step_stepStar (by simp [fm] :
    ⟨2, B + 4, 0, 0, e + 1⟩ [fm]⊢ ⟨1, B + 4, 0, 1, e + 2⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] :
    ⟨1, B + 4, 0, 1, e + 2⟩ [fm]⊢ ⟨0, B + 4, 0, 2, e + 3⟩))
  rw [show B + 4 = (B + 3) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain (B + 3) 1 (e + 3)); ring_nf; finish

-- r=4: (0, B+1, 4, 2, e+1) → 8 tail steps then drain
-- R3,R1,R1,R3,R1,R1,R5,R2 then drain(B+5, 2, e+1)
theorem tail4_drain : ∀ B, ⟨0, B + 1, 4, 2, e + 1⟩ [fm]⊢⁺
    ⟨2, 0, 0, B + 8, e + 2 * B + 13⟩ := by
  intro B
  rw [show (4 : ℕ) = 3 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show B + 0 + 2 + 2 = (B + 3) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show (B + 3) + 0 + 2 + 2 = B + 7 from by ring]
  -- State after rw: (0, B+7, 0, 0, e+1+0+1) or (0, B+7, 0, 0, e+1).
  -- The +0+1 issue: step fm set e to e+1+0+1 from R1 pattern.
  -- Actually: after the 6 step fm's, the last R1 gives e unchanged.
  -- Let me just use simp for the R5 and R2 steps.
  apply stepStar_trans (step_stepStar (by simp [fm] :
    ⟨0, B + 7, 0, 0, e + 1⟩ [fm]⊢ ⟨1, B + 7, 0, 2, e⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] :
    ⟨1, B + 7, 0, 2, e⟩ [fm]⊢ ⟨0, B + 7, 0, 3, e + 1⟩))
  rw [show B + 7 = (B + 6) + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (drain (B + 6) 2 (e + 1)); ring_nf; finish

-- d ≡ 2 mod 5
theorem trans_A : ⟨2, 0, 0, 5 * m + 2, F + m⟩ [fm]⊢⁺
    ⟨2, 0, 0, 8 * m + 5, F + 16 * m + 12⟩ := by
  step fm; step fm
  rw [show 5 * m + 2 + 1 + 1 = 0 + (5 * m + 4) from by ring,
      show F + m + 1 + 1 = F + m + 2 from by ring]
  apply stepStar_trans (d_to_c (5 * m + 4) (c := 0) (d := 0) (e := F + m + 2))
  rw [show 0 + (5 * m + 4) = 3 + 5 * m + 1 from by ring,
      show F + m + 2 = (F + 1) + m + 1 from by ring]
  apply stepStar_trans (open_spiral m (c := 3) (e := F + 1))
  rw [show 2 + 8 * m = (1 + 8 * m) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (tail3_drain (1 + 8 * m) (e := F + 1)))
  ring_nf; finish

-- d ≡ 3 mod 5
theorem trans_B : ⟨2, 0, 0, 5 * m + 3, F + m⟩ [fm]⊢⁺
    ⟨2, 0, 0, 8 * m + 9, F + 16 * m + 15⟩ := by
  step fm; step fm
  rw [show 5 * m + 3 + 1 + 1 = 0 + (5 * m + 5) from by ring,
      show F + m + 1 + 1 = F + m + 2 from by ring]
  apply stepStar_trans (d_to_c (5 * m + 5) (c := 0) (d := 0) (e := F + m + 2))
  rw [show 0 + (5 * m + 5) = 4 + 5 * m + 1 from by ring,
      show F + m + 2 = (F + 1) + m + 1 from by ring]
  apply stepStar_trans (open_spiral m (c := 4) (e := F + 1))
  rw [show 2 + 8 * m = (1 + 8 * m) + 1 from by ring]
  apply stepStar_trans (stepPlus_stepStar (tail4_drain (1 + 8 * m) (e := F)))
  ring_nf; finish

-- d ≡ 4 mod 5: direct drain after open_spiral
theorem trans_C : ⟨2, 0, 0, 5 * m + 4, F + m + 1⟩ [fm]⊢⁺
    ⟨2, 0, 0, 8 * m + 10, F + 16 * m + 19⟩ := by
  step fm; step fm
  rw [show 5 * m + 4 + 1 + 1 = 0 + (5 * m + 6) from by ring,
      show F + m + 1 + 1 + 1 = F + m + 3 from by ring]
  apply stepStar_trans (d_to_c (5 * m + 6) (c := 0) (d := 0) (e := F + m + 3))
  rw [show 0 + (5 * m + 6) = 0 + 5 * (m + 1) + 1 from by ring,
      show F + m + 3 = (F + 1) + (m + 1) + 1 from by ring]
  apply stepStar_trans (open_spiral (m + 1) (c := 0) (e := F + 1))
  rw [show 2 + 8 * (m + 1) = (9 + 8 * m) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain (9 + 8 * m) 1 (F + 1)); ring_nf; finish

-- d ≡ 0 mod 5: tail r=1 (3 steps) then drain
theorem trans_D : ⟨2, 0, 0, 5 * m + 5, F + m + 1⟩ [fm]⊢⁺
    ⟨2, 0, 0, 8 * m + 11, F + 16 * m + 22⟩ := by
  step fm; step fm
  rw [show 5 * m + 5 + 1 + 1 = 0 + (5 * m + 7) from by ring,
      show F + m + 1 + 1 + 1 = F + m + 3 from by ring]
  apply stepStar_trans (d_to_c (5 * m + 7) (c := 0) (d := 0) (e := F + m + 3))
  rw [show 0 + (5 * m + 7) = 1 + 5 * (m + 1) + 1 from by ring,
      show F + m + 3 = (F + 1) + (m + 1) + 1 from by ring]
  apply stepStar_trans (open_spiral (m + 1) (c := 1) (e := F + 1))
  rw [show 2 + 8 * (m + 1) = (9 + 8 * m) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show (9 + 8 * m) + 0 + 2 = (10 + 8 * m) + 1 from by ring,
      show F + 1 + 0 + 1 = F + 2 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain (10 + 8 * m) 1 (F + 2)); ring_nf; finish

-- d ≡ 1 mod 5: tail r=2 (6 steps) then drain
theorem trans_E : ⟨2, 0, 0, 5 * m + 6, F + m + 1⟩ [fm]⊢⁺
    ⟨2, 0, 0, 8 * m + 12, F + 16 * m + 25⟩ := by
  step fm; step fm
  rw [show 5 * m + 6 + 1 + 1 = 0 + (5 * m + 8) from by ring,
      show F + m + 1 + 1 + 1 = F + m + 3 from by ring]
  apply stepStar_trans (d_to_c (5 * m + 8) (c := 0) (d := 0) (e := F + m + 3))
  rw [show 0 + (5 * m + 8) = 2 + 5 * (m + 1) + 1 from by ring,
      show F + m + 3 = (F + 1) + (m + 1) + 1 from by ring]
  apply stepStar_trans (open_spiral (m + 1) (c := 2) (e := F + 1))
  rw [show 2 + 8 * (m + 1) = (9 + 8 * m) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show 9 + 8 * m + 2 + 2 = (12 + 8 * m) + 1 from by ring]
  step fm
  -- State: (2, 12+8m, 0, 0, F+1). R2 fires (a=2,c=0).
  apply stepStar_trans (step_stepStar (by simp [fm] :
    ⟨2, 12 + 8 * m, 0, 0, F + 1⟩ [fm]⊢ ⟨1, 12 + 8 * m, 0, 1, F + 2⟩))
  apply stepStar_trans (step_stepStar (by simp [fm] :
    ⟨1, 12 + 8 * m, 0, 1, F + 2⟩ [fm]⊢ ⟨0, 12 + 8 * m, 0, 2, F + 3⟩))
  rw [show 12 + 8 * m = (11 + 8 * m) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain (11 + 8 * m) 1 (F + 3)); ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 2⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨2, 0, 0, d, e⟩ ∧ d ≥ 2 ∧ e ≥ d)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    obtain ⟨n, rfl | rfl | rfl | rfl | rfl⟩ :
        ∃ n, d = 5 * n + 2 ∨ d = 5 * n + 3 ∨ d = 5 * n + 4 ∨ d = 5 * n + 5 ∨ d = 5 * n + 6 :=
      ⟨(d - 2) / 5, by omega⟩
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + n := ⟨e - n, by omega⟩
      exact ⟨⟨2, 0, 0, 8 * n + 5, F + 16 * n + 12⟩,
        ⟨8 * n + 5, F + 16 * n + 12, rfl, by omega, by omega⟩, trans_A⟩
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + n := ⟨e - n, by omega⟩
      exact ⟨⟨2, 0, 0, 8 * n + 9, F + 16 * n + 15⟩,
        ⟨8 * n + 9, F + 16 * n + 15, rfl, by omega, by omega⟩, trans_B⟩
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + n + 1 := ⟨e - n - 1, by omega⟩
      exact ⟨⟨2, 0, 0, 8 * n + 10, F + 16 * n + 19⟩,
        ⟨8 * n + 10, F + 16 * n + 19, rfl, by omega, by omega⟩, trans_C⟩
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + n + 1 := ⟨e - n - 1, by omega⟩
      exact ⟨⟨2, 0, 0, 8 * n + 11, F + 16 * n + 22⟩,
        ⟨8 * n + 11, F + 16 * n + 22, rfl, by omega, by omega⟩, trans_D⟩
    · obtain ⟨F, rfl⟩ : ∃ F, e = F + n + 1 := ⟨e - n - 1, by omega⟩
      exact ⟨⟨2, 0, 0, 8 * n + 12, F + 16 * n + 25⟩,
        ⟨8 * n + 12, F + 16 * n + 25, rfl, by omega, by omega⟩, trans_E⟩
  · exact ⟨2, 2, rfl, by omega, by omega⟩
