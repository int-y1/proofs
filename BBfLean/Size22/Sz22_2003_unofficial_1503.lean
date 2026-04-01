import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1503: [7/15, 9/77, 242/3, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1503

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R4 chain: drain e in pairs into c (b=0, d=0)
theorem r4_chain : ∀ k, ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 1))
    ring_nf; finish

-- R5/R1 pairs: with e=0, drain c into d while consuming a
theorem r5r1_pairs : ∀ n, ⟨a + n, 0, n, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * n, 0⟩ := by
  intro n; induction' n with n ih generalizing a d
  · exists 0
  · rw [show a + (n + 1) = (a + n) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a) (d := d + 2))
    ring_nf; finish

-- R3 drain: with c=0, d=0, drain b into a and e
theorem r3_drain : ∀ b, ⟨a, b, 0, 0, e⟩ [fm]⊢* ⟨a + b, 0, 0, 0, e + 2 * b⟩ := by
  intro b; induction' b with b ih generalizing a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 2))
    ring_nf; finish

-- R2/R3 chain: 3-step cycles reducing d by 2 each.
-- Uses simp [fm] for the R3 step due to symbolic d.
theorem r2r3_chain : ∀ k, ⟨a, b, 0, d + 2 * k, 2⟩ [fm]⊢* ⟨a + k, b + 3 * k, 0, d, 2⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (step_stepStar (show (⟨a, b + 4, 0, d + 2 * k, 0⟩ : Q) [fm]⊢
      ⟨a + 1, b + 3, 0, d + 2 * k, 2⟩ from by simp [fm]))
    apply stepStar_trans (ih (a := a + 1) (b := b + 3))
    ring_nf; finish

-- Even drain: from (a+1+c, 0, c, 0, 0) to (a+1, 0, 0, 2c+1, 2)
theorem drain_even : ∀ c, ⟨a + 1 + c, 0, c, 0, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, 2 * c + 1, 2⟩ := by
  intro c
  apply stepStar_trans (r5r1_pairs c (a := a + 1) (d := 0))
  rw [show 0 + 2 * c = 2 * c from by ring]
  apply stepStar_trans (step_stepStar (show (⟨a + 1, 0, 0, 2 * c, 0⟩ : Q) [fm]⊢
    ⟨a, 1, 0, 2 * c + 1, 0⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar (show (⟨a, 1, 0, 2 * c + 1, 0⟩ : Q) [fm]⊢
    ⟨a + 1, 0, 0, 2 * c + 1, 2⟩ from by simp [fm]))
  finish

-- Odd drain: from (a+C+2, 0, C+2, 0, 1) to (a+2, 0, 0, 2C+2, 2)
theorem drain_odd : ∀ C, ⟨a + C + 2, 0, C + 2, 0, 1⟩ [fm]⊢* ⟨a + 2, 0, 0, 2 * C + 2, 2⟩ := by
  intro C; cases C with
  | zero =>
    step fm; step fm; step fm; step fm; step fm; finish
  | succ C' =>
    rw [show a + (C' + 1) + 2 = (a + C' + 2) + 1 from by ring,
        show (C' + 1) + 2 = (C' + 2) + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm
    show ⟨a + C' + 2, 0, C', 3, 0⟩ [fm]⊢* ⟨a + 2, 0, 0, 2 * (C' + 1) + 2, 2⟩
    rw [show a + C' + 2 = (a + 2) + C' from by ring]
    apply stepStar_trans (r5r1_pairs C' (a := a + 2) (d := 3))
    rw [show 3 + 2 * C' = 2 * C' + 3 from by ring,
        show 2 * (C' + 1) + 2 = 2 * C' + 4 from by ring]
    apply stepStar_trans (step_stepStar (show (⟨a + 2, 0, 0, 2 * C' + 3, 0⟩ : Q) [fm]⊢
      ⟨a + 1, 1, 0, 2 * C' + 4, 0⟩ from by simp [fm]))
    apply stepStar_trans (step_stepStar (show (⟨a + 1, 1, 0, 2 * C' + 4, 0⟩ : Q) [fm]⊢
      ⟨a + 2, 0, 0, 2 * C' + 4, 2⟩ from by simp [fm]))
    finish

-- Phases 1-5: from even canonical to odd intermediate
-- (n+k+5, 0, 0, 0, 2k+8) →* (n+4k+19, 0, 0, 0, 6k+29)
theorem even_to_odd_star :
    ⟨n + k + 5, 0, 0, 0, 2 * k + 8⟩ [fm]⊢* ⟨n + 4 * k + 19, 0, 0, 0, 6 * k + 29⟩ := by
  -- Phase 1: R4 chain (k+4 steps)
  rw [show 2 * k + 8 = 0 + 2 * (k + 4) from by ring]
  apply stepStar_trans (r4_chain (k + 4) (a := n + k + 5) (c := 0) (e := 0))
  -- After: ⟨n+k+5, 0, k+4, 0, 0⟩
  show ⟨n + k + 5, 0, 0 + (k + 4), 0, 0⟩ [fm]⊢* _
  rw [show 0 + (k + 4) = k + 4 from by ring,
      show n + k + 5 = n + 1 + (k + 4) from by ring]
  -- Phase 2: drain_even
  apply stepStar_trans (drain_even (k + 4) (a := n))
  -- After: ⟨n+1, 0, 0, 2(k+4)+1, 2⟩
  -- Phase 3: r2r3_chain (k+4 cycles)
  rw [show 2 * (k + 4) + 1 = 1 + 2 * (k + 4) from by ring]
  apply stepStar_trans (r2r3_chain (k + 4) (a := n + 1) (b := 0) (d := 1))
  -- After: ⟨n+k+5, 3k+12, 0, 1, 2⟩
  -- Phase 4: R2 terminal
  show ⟨n + 1 + (k + 4), 0 + 3 * (k + 4), 0, 1, 2⟩ [fm]⊢* _
  rw [show n + 1 + (k + 4) = n + k + 5 from by ring,
      show 0 + 3 * (k + 4) = 3 * k + 12 from by ring]
  apply stepStar_trans (step_stepStar (show (⟨n + k + 5, 3 * k + 12, 0, 1, 2⟩ : Q) [fm]⊢
    ⟨n + k + 5, 3 * k + 14, 0, 0, 1⟩ from by simp [fm]))
  -- Phase 5: r3_drain
  apply stepStar_trans (r3_drain (3 * k + 14) (a := n + k + 5) (e := 1))
  ring_nf; finish

-- Phases 6-9: from odd intermediate to next even canonical
-- (n+4k+19, 0, 0, 0, 6k+29) →* (n+13k+59, 0, 0, 0, 18k+80)
theorem odd_to_even_star :
    ⟨n + 4 * k + 19, 0, 0, 0, 6 * k + 29⟩ [fm]⊢* ⟨n + 13 * k + 59, 0, 0, 0, 18 * k + 80⟩ := by
  -- Phase 6: R4 chain, e = 6k+29 = 1 + 2*(3k+14)
  rw [show 6 * k + 29 = 1 + 2 * (3 * k + 14) from by ring]
  apply stepStar_trans (r4_chain (3 * k + 14) (a := n + 4 * k + 19) (c := 0) (e := 1))
  -- After: ⟨n+4k+19, 0, 3k+14, 0, 1⟩
  -- Phase 7: drain_odd (C = 3k+12, C+2 = 3k+14)
  show ⟨n + 4 * k + 19, 0, 0 + (3 * k + 14), 0, 1⟩ [fm]⊢* _
  rw [show 0 + (3 * k + 14) = (3 * k + 12) + 2 from by ring,
      show n + 4 * k + 19 = (n + k + 5) + (3 * k + 12) + 2 from by ring]
  apply stepStar_trans (drain_odd (3 * k + 12) (a := n + k + 5))
  -- After: ⟨n+k+7, 0, 0, 6k+26, 2⟩
  -- Phase 8: r2r3_chain (3k+13 cycles)
  show ⟨(n + k + 5) + 2, 0, 0, 2 * (3 * k + 12) + 2, 2⟩ [fm]⊢* _
  rw [show (n + k + 5) + 2 = n + k + 7 from by ring,
      show 2 * (3 * k + 12) + 2 = 0 + 2 * (3 * k + 13) from by ring]
  apply stepStar_trans (r2r3_chain (3 * k + 13) (a := n + k + 7) (b := 0) (d := 0))
  -- After: ⟨n+4k+20, 9k+39, 0, 0, 2⟩
  -- Phase 9: r3_drain
  show ⟨n + k + 7 + (3 * k + 13), 0 + 3 * (3 * k + 13), 0, 0, 2⟩ [fm]⊢* _
  rw [show n + k + 7 + (3 * k + 13) = n + 4 * k + 20 from by ring,
      show 0 + 3 * (3 * k + 13) = 9 * k + 39 from by ring]
  apply stepStar_trans (r3_drain (9 * k + 39) (a := n + 4 * k + 20) (e := 2))
  ring_nf; finish

-- Full composite transition (⊢⁺)
theorem main_trans :
    ⟨n + k + 5, 0, 0, 0, 2 * k + 8⟩ [fm]⊢⁺ ⟨n + 13 * k + 59, 0, 0, 0, 18 * k + 80⟩ := by
  apply stepStar_stepPlus_stepPlus even_to_odd_star
  -- Need: ⟨n+4k+19, 0, 0, 0, 6k+29⟩ ⊢⁺ ⟨n+13k+59, 0, 0, 0, 18k+80⟩
  -- First step of odd_to_even is R4 (e = 6k+29 ≥ 2 since k ≥ 0)
  rw [show 6 * k + 29 = (6 * k + 27) + 2 from by ring]
  step fm
  -- After one R4: ⟨n+4k+19, 0, 1, 0, 6k+27⟩
  -- Remaining: odd_to_even minus one R4 step
  show ⟨n + 4 * k + 19, 0, 1, 0, 6 * k + 27⟩ [fm]⊢* _
  rw [show 6 * k + 27 = 1 + 2 * (3 * k + 13) from by ring]
  apply stepStar_trans (r4_chain (3 * k + 13) (a := n + 4 * k + 19) (c := 1) (e := 1))
  -- After: ⟨n+4k+19, 0, 3k+14, 0, 1⟩
  show ⟨n + 4 * k + 19, 0, 1 + (3 * k + 13), 0, 1⟩ [fm]⊢* _
  rw [show 1 + (3 * k + 13) = (3 * k + 12) + 2 from by ring,
      show n + 4 * k + 19 = (n + k + 5) + (3 * k + 12) + 2 from by ring]
  apply stepStar_trans (drain_odd (3 * k + 12) (a := n + k + 5))
  show ⟨(n + k + 5) + 2, 0, 0, 2 * (3 * k + 12) + 2, 2⟩ [fm]⊢* _
  rw [show (n + k + 5) + 2 = n + k + 7 from by ring,
      show 2 * (3 * k + 12) + 2 = 0 + 2 * (3 * k + 13) from by ring]
  apply stepStar_trans (r2r3_chain (3 * k + 13) (a := n + k + 7) (b := 0) (d := 0))
  show ⟨n + k + 7 + (3 * k + 13), 0 + 3 * (3 * k + 13), 0, 0, 2⟩ [fm]⊢* _
  rw [show n + k + 7 + (3 * k + 13) = n + 4 * k + 20 from by ring,
      show 0 + 3 * (3 * k + 13) = 9 * k + 39 from by ring]
  apply stepStar_trans (r3_drain (9 * k + 39) (a := n + 4 * k + 20) (e := 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 8⟩)
  · execute fm 18
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, k⟩ ↦ ⟨n + k + 5, 0, 0, 0, 2 * k + 8⟩) ⟨2, 0⟩
  intro ⟨n, k⟩
  exact ⟨⟨n + 4 * k + 18, 9 * k + 36⟩, by
    show ⟨n + k + 5, 0, 0, 0, 2 * k + 8⟩ [fm]⊢⁺
      ⟨(n + 4 * k + 18) + (9 * k + 36) + 5, 0, 0, 0, 2 * (9 * k + 36) + 8⟩
    rw [show (n + 4 * k + 18) + (9 * k + 36) + 5 = n + 13 * k + 59 from by ring,
        show 2 * (9 * k + 36) + 8 = 18 * k + 80 from by ring]
    exact main_trans⟩

end Sz22_2003_unofficial_1503
