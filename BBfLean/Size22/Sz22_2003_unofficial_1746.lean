import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1746: [8/15, 9/14, 55/2, 7/5, 10/11]

Vector representation:
```
 3 -1 -1  0  0
-1  2  0 -1  0
-1  0  1  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1746

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R3 repeated: (a+k, 0, c, 0, e) ⊢* (a, 0, c+k, 0, e+k) when b=0, d=0
theorem r3_chain : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (c := c + 1) (e := e + 1))
    ring_nf; finish

-- R4 repeated: (0, 0, c+k, d, e) ⊢* (0, 0, c, d+k, e) when a=0, b=0
theorem r4_chain : ∀ k, ⟨0, 0, c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c) (d := d + 1) (e := e))
    ring_nf; finish

-- R1+R3 loop: (a+1, k+1, 0, 0, e) ⊢* (a+2k+3, 0, 0, 0, e+k+1)
theorem r1r3_loop : ∀ k, ⟨a + 1, k + 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k + 3, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a e
  · step fm; step fm; finish
  · step fm; step fm
    rw [show (a + 1) + 2 = (a + 2) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

-- Single drain cycle: (0, b+1, 0, d+4, e+1) ⊢* (0, b+8, 0, d, e)
-- R5, R1, R2 x4
theorem drain_cycle_step : ⟨0, b + 1, 0, d + 4, e + 1⟩ [fm]⊢* ⟨0, b + 8, 0, d, e⟩ := by
  rw [show d + 4 = d + 3 + 1 from by ring, show e + 1 = e + 1 from rfl]
  step fm
  rw [show b + 1 = b + 1 from rfl]
  step fm
  rw [show d + 3 + 1 = d + 3 + 1 from rfl]
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Iterated drain cycles
theorem iter_drain : ∀ k, ⟨0, b + 1, 0, d + 4 * k, e + k⟩ [fm]⊢* ⟨0, b + 7 * k + 1, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show d + 4 * (k + 1) = (d + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b) (d := d + 4) (e := e + 1))
    rw [show b + 7 * k + 1 = (b + 7 * k) + 1 from by ring]
    apply stepStar_trans (drain_cycle_step (b := b + 7 * k) (d := d) (e := e))
    rw [show b + 7 * k + 8 = b + 7 * (k + 1) + 1 from by ring]
    finish

theorem drain_base1 : ⟨0, 0, 0, 1, F + 1⟩ [fm]⊢⁺ ⟨5, 0, 0, 0, F + 1⟩ := by
  execute fm 5

theorem drain_base2 : ⟨0, 0, 0, 2, F + 2⟩ [fm]⊢⁺ ⟨8, 0, 0, 0, F + 4⟩ := by
  execute fm 10

theorem drain_base3 : ⟨0, 0, 0, 3, F + 3⟩ [fm]⊢⁺ ⟨11, 0, 0, 0, F + 7⟩ := by
  execute fm 15

theorem drain_base4 : ⟨0, 0, 0, 4, F + 4⟩ [fm]⊢⁺ ⟨16, 0, 0, 0, F + 8⟩ := by
  execute fm 20

-- For D = 4m+5: opening 6 steps, iter_drain m, end case (3 steps + R1R3 loop)
theorem drain_ind1 : ⟨0, 0, 0, 4 * m + 5, F + 4 * m + 5⟩ [fm]⊢⁺
    ⟨14 * m + 19, 0, 0, 0, F + 10 * m + 11⟩ := by
  -- Opening: 6 steps to (0, 7, 0, 4*m+1, F+4*m+4)
  step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨0, 7, 0, 4 * m + 1, F + 4 * m + 4⟩ [fm]⊢* _
  -- iter_drain: b=6, d=1, k=m
  rw [show (7 : ℕ) = 6 + 1 from by ring,
      show 4 * m + 1 = 1 + 4 * m from by ring,
      show F + 4 * m + 4 = (F + 3 * m + 4) + m from by ring]
  apply stepStar_trans (iter_drain m (b := 6) (d := 1) (e := F + 3 * m + 4))
  -- After iter_drain: (0, 7m+7, 0, 1, F+3m+4)
  -- End case: R5, R1, R2 (3 steps) to (3, 7m+8, 0, 0, F+3m+3)
  rw [show 6 + 7 * m + 1 = 7 * m + 7 from by ring]
  -- Need to handle (0, 7*m+7, 0, 1, F+3*m+4)
  -- R5: e = F+3*m+4 = (F+3*m+3)+1
  rw [show F + 3 * m + 4 = (F + 3 * m + 3) + 1 from by ring]
  step fm
  -- Now: (1, 7*m+7, 1, 1, F+3*m+3)
  -- R1: b = 7*m+7 = (7*m+6)+1, c = 1 = 0+1
  rw [show 7 * m + 7 = (7 * m + 6) + 1 from by ring]
  step fm
  -- Now: (4, 7*m+6, 0, 1, F+3*m+3)
  -- R2: a = 4 = 3+1, d = 1 = 0+1
  step fm
  -- Now: (3, 7*m+8, 0, 0, F+3*m+3)
  show ⟨3, 7 * m + 8, 0, 0, F + 3 * m + 3⟩ [fm]⊢* _
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 7 * m + 8 = (7 * m + 7) + 1 from by ring]
  apply stepStar_trans (r1r3_loop (7 * m + 7) (a := 2) (e := F + 3 * m + 3))
  ring_nf; finish

theorem drain_ind2 : ⟨0, 0, 0, 4 * m + 6, F + 4 * m + 6⟩ [fm]⊢⁺
    ⟨14 * m + 22, 0, 0, 0, F + 10 * m + 14⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨0, 7, 0, 4 * m + 2, F + 4 * m + 5⟩ [fm]⊢* _
  rw [show (7 : ℕ) = 6 + 1 from by ring,
      show 4 * m + 2 = 2 + 4 * m from by ring,
      show F + 4 * m + 5 = (F + 3 * m + 5) + m from by ring]
  apply stepStar_trans (iter_drain m (b := 6) (d := 2) (e := F + 3 * m + 5))
  rw [show 6 + 7 * m + 1 = 7 * m + 7 from by ring]
  -- (0, 7m+7, 0, 2, F+3m+5)
  -- R5: e = F+3m+5 = (F+3m+4)+1
  rw [show F + 3 * m + 5 = (F + 3 * m + 4) + 1 from by ring]
  step fm
  -- (1, 7m+7, 1, 2, F+3m+4)
  rw [show 7 * m + 7 = (7 * m + 6) + 1 from by ring]
  step fm
  -- (4, 7m+6, 0, 2, F+3m+4): R2
  step fm
  -- (3, 7m+8, 0, 1, F+3m+4): R2
  step fm
  -- (2, 7m+10, 0, 0, F+3m+4): R3
  step fm
  -- (1, 7m+10, 1, 0, F+3m+5): R1
  rw [show 7 * m + 10 = (7 * m + 9) + 1 from by ring]
  step fm
  -- (4, 7m+9, 0, 0, F+3m+5)
  show ⟨4, 7 * m + 9, 0, 0, F + 3 * m + 5⟩ [fm]⊢* _
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 7 * m + 9 = (7 * m + 8) + 1 from by ring]
  apply stepStar_trans (r1r3_loop (7 * m + 8) (a := 3) (e := F + 3 * m + 5))
  ring_nf; finish

theorem drain_ind3 : ⟨0, 0, 0, 4 * m + 7, F + 4 * m + 7⟩ [fm]⊢⁺
    ⟨14 * m + 25, 0, 0, 0, F + 10 * m + 17⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨0, 7, 0, 4 * m + 3, F + 4 * m + 6⟩ [fm]⊢* _
  rw [show (7 : ℕ) = 6 + 1 from by ring,
      show 4 * m + 3 = 3 + 4 * m from by ring,
      show F + 4 * m + 6 = (F + 3 * m + 6) + m from by ring]
  apply stepStar_trans (iter_drain m (b := 6) (d := 3) (e := F + 3 * m + 6))
  rw [show 6 + 7 * m + 1 = 7 * m + 7 from by ring]
  -- (0, 7m+7, 0, 3, F+3m+6)
  rw [show F + 3 * m + 6 = (F + 3 * m + 5) + 1 from by ring]
  step fm
  rw [show 7 * m + 7 = (7 * m + 6) + 1 from by ring]
  step fm
  -- (4, 7m+6, 0, 3, F+3m+5)
  step fm; step fm; step fm
  -- (1, 7m+12, 0, 0, F+3m+5): R3
  step fm
  -- (0, 7m+12, 1, 0, F+3m+6): R1
  rw [show 7 * m + 12 = (7 * m + 11) + 1 from by ring]
  step fm
  -- (3, 7m+11, 0, 0, F+3m+6)
  show ⟨3, 7 * m + 11, 0, 0, F + 3 * m + 6⟩ [fm]⊢* _
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 7 * m + 11 = (7 * m + 10) + 1 from by ring]
  apply stepStar_trans (r1r3_loop (7 * m + 10) (a := 2) (e := F + 3 * m + 6))
  ring_nf; finish

theorem drain_ind4 : ⟨0, 0, 0, 4 * m + 8, F + 4 * m + 8⟩ [fm]⊢⁺
    ⟨14 * m + 30, 0, 0, 0, F + 10 * m + 18⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨0, 7, 0, 4 * m + 4, F + 4 * m + 7⟩ [fm]⊢* _
  rw [show (7 : ℕ) = 6 + 1 from by ring,
      show 4 * m + 4 = 0 + 4 * (m + 1) from by ring,
      show F + 4 * m + 7 = (F + 3 * m + 6) + (m + 1) from by ring]
  apply stepStar_trans (iter_drain (m + 1) (b := 6) (d := 0) (e := F + 3 * m + 6))
  rw [show 6 + 7 * (m + 1) + 1 = 7 * m + 14 from by ring]
  -- (0, 7m+14, 0, 0, F+3m+6)
  -- R5: e = F+3m+6 = (F+3m+5)+1
  rw [show F + 3 * m + 6 = (F + 3 * m + 5) + 1 from by ring]
  step fm
  -- (1, 7m+14, 1, 0, F+3m+5): R1
  rw [show 7 * m + 14 = (7 * m + 13) + 1 from by ring]
  step fm
  -- (4, 7m+13, 0, 0, F+3m+5)
  show ⟨4, 7 * m + 13, 0, 0, F + 3 * m + 5⟩ [fm]⊢* _
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 7 * m + 13 = (7 * m + 12) + 1 from by ring]
  apply stepStar_trans (r1r3_loop (7 * m + 12) (a := 3) (e := F + 3 * m + 5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨5, 0, 0, 0, 1⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    have phases12 : ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, a + 1, e + a + 1⟩ := by
      have h1 := r3_chain (a + 1) (a := 0) (c := 0) (e := e)
      rw [show 0 + (a + 1) = a + 1 from by ring] at h1
      have h2 := r4_chain (a + 1) (c := 0) (d := 0) (e := e + (a + 1))
      rw [show 0 + (a + 1) = a + 1 from by ring,
          show e + (a + 1) = e + a + 1 from by ring] at h2
      exact stepStar_trans h1 h2
    obtain ⟨n, rfl | rfl | rfl | rfl⟩ : ∃ n, a = 4 * n ∨ a = 4 * n + 1 ∨ a = 4 * n + 2 ∨ a = 4 * n + 3 :=
      ⟨a / 4, by omega⟩
    · -- a = 4*n, a+1 = 4*n+1
      refine ⟨⟨14 * n + 5, 0, 0, 0, e + 10 * n + 1⟩,
        ⟨14 * n + 4, e + 10 * n + 1, rfl⟩, ?_⟩
      apply stepStar_stepPlus_stepPlus phases12
      rw [show e + 4 * n + 1 = e + 4 * n + 1 from rfl]
      rcases n with _ | m
      · exact drain_base1
      · rw [show 4 * (m + 1) + 1 = 4 * m + 5 from by ring,
            show e + (4 * (m + 1)) + 1 = e + 4 * m + 5 from by ring,
            show 14 * (m + 1) + 5 = 14 * m + 19 from by ring,
            show e + 10 * (m + 1) + 1 = e + 10 * m + 11 from by ring]
        exact drain_ind1
    · -- a = 4*n+1, a+1 = 4*n+2
      refine ⟨⟨14 * n + 8, 0, 0, 0, e + 10 * n + 4⟩,
        ⟨14 * n + 7, e + 10 * n + 4, rfl⟩, ?_⟩
      apply stepStar_stepPlus_stepPlus phases12
      rw [show 4 * n + 1 + 1 = 4 * n + 2 from by ring,
          show e + (4 * n + 1) + 1 = e + 4 * n + 2 from by ring]
      rcases n with _ | m
      · exact drain_base2
      · rw [show 4 * (m + 1) + 2 = 4 * m + 6 from by ring,
            show e + 4 * (m + 1) + 2 = e + 4 * m + 6 from by ring,
            show 14 * (m + 1) + 8 = 14 * m + 22 from by ring,
            show e + 10 * (m + 1) + 4 = e + 10 * m + 14 from by ring]
        exact drain_ind2
    · -- a = 4*n+2, a+1 = 4*n+3
      refine ⟨⟨14 * n + 11, 0, 0, 0, e + 10 * n + 7⟩,
        ⟨14 * n + 10, e + 10 * n + 7, rfl⟩, ?_⟩
      apply stepStar_stepPlus_stepPlus phases12
      rw [show 4 * n + 2 + 1 = 4 * n + 3 from by ring,
          show e + (4 * n + 2) + 1 = e + 4 * n + 3 from by ring]
      rcases n with _ | m
      · exact drain_base3
      · rw [show 4 * (m + 1) + 3 = 4 * m + 7 from by ring,
            show e + 4 * (m + 1) + 3 = e + 4 * m + 7 from by ring,
            show 14 * (m + 1) + 11 = 14 * m + 25 from by ring,
            show e + 10 * (m + 1) + 7 = e + 10 * m + 17 from by ring]
        exact drain_ind3
    · -- a = 4*n+3, a+1 = 4*(n+1)
      refine ⟨⟨14 * n + 16, 0, 0, 0, e + 10 * n + 8⟩,
        ⟨14 * n + 15, e + 10 * n + 8, rfl⟩, ?_⟩
      apply stepStar_stepPlus_stepPlus phases12
      rw [show 4 * n + 3 + 1 = 4 * (n + 1) from by ring,
          show e + (4 * n + 3) + 1 = e + 4 * (n + 1) from by ring]
      rcases n with _ | m
      · rw [show 4 * (0 + 1) = 4 from by ring,
            show e + 4 * (0 + 1) = e + 4 from by ring,
            show 14 * 0 + 16 = 16 from by ring,
            show e + 10 * 0 + 8 = e + 8 from by ring]
        exact drain_base4
      · have goal_rw : (0, 0, 0, 4 * ((m + 1) + 1), e + 4 * ((m + 1) + 1)) =
            (0, 0, 0, 4 * m + 8, e + 4 * m + 8) := by ring_nf
        rw [goal_rw]
        have res_rw : (14 * (m + 1) + 16, 0, 0, 0, e + 10 * (m + 1) + 8) =
            (14 * m + 30, 0, 0, 0, e + 10 * m + 18) := by ring_nf
        rw [res_rw]
        exact drain_ind4
  · exact ⟨4, 1, rfl⟩
