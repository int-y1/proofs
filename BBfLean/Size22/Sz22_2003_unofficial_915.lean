import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #915: [4/15, 3/14, 605/2, 49/5, 10/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  2
 0  0 -1  2  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_915

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- Phase 1: R3 drains a, builds c and e
theorem r3_chain : ∀ k, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [Nat.add_succ a k]; step fm
    apply stepStar_trans (ih (a := a) (c := c + 1) (e := e + 2)); ring_nf; finish

-- Phase 2: R4 drains c, builds d
theorem r4_chain : ∀ k, ⟨0, 0, c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c := c) (d := d + 2)); ring_nf; finish

-- Combined: (A+1, 0, 0, 0, E) ->* (0, 0, 0, 2A+2, E+2A+2)
theorem r3_r4 : ⟨a + 1, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 2, e + 2 * a + 2⟩ := by
  apply stepStar_trans
  · rw [show a + 1 = 0 + (a + 1) from by ring]
    exact r3_chain (a + 1) (a := 0) (c := 0) (e := e)
  apply stepStar_trans (r4_chain (a + 1) (c := 0) (d := 0) (e := e + 2 * (a + 1)))
  ring_nf; finish

-- Staircase round b=0: R5 R2 R1 R2 R2
theorem staircase_b0 : ⟨0, 0, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, 2, 0, d, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Staircase round b>=1: R5 R1 R2 R2 R2
theorem staircase_bpos : ⟨0, b + 1, 0, d + 3, e + 1⟩ [fm]⊢* ⟨0, b + 3, 0, d, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Staircase loop
theorem staircase_loop : ∀ K, ⟨0, b, 0, 3 * K + r, e + K⟩ [fm]⊢*
    ⟨0, b + 2 * K, 0, r, e⟩ := by
  intro K; induction' K with K ih generalizing b e
  · ring_nf; finish
  · rw [show 3 * (K + 1) + r = (3 * K + r) + 3 from by ring,
        show e + (K + 1) = (e + K) + 1 from by ring]
    rcases b with _ | b'
    · apply stepStar_trans staircase_b0
      rw [show (2 : ℕ) = 0 + 2 from by ring]
      apply stepStar_trans (ih (b := 0 + 2) (e := e))
      ring_nf; finish
    · apply stepStar_trans staircase_bpos
      rw [show b' + 3 = (b' + 1) + 2 from by ring]
      apply stepStar_trans (ih (b := b' + 1 + 2) (e := e))
      ring_nf; finish

-- Tail d=2 b=0: R5 R2 R1 R2
theorem tail_d2_b0 : ⟨0, 0, 0, 2, e + 1⟩ [fm]⊢* ⟨1, 1, 0, 0, e⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Tail d=2 b>=1: R5 R1 R2 R2
theorem tail_d2_bpos : ⟨0, b + 1, 0, 2, e + 1⟩ [fm]⊢* ⟨1, b + 2, 0, 0, e⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Tail d=1 b=0: R5 R2 R1
theorem tail_d1_b0 : ⟨0, 0, 0, 1, e + 1⟩ [fm]⊢* ⟨2, 0, 0, 0, e⟩ := by
  step fm; step fm; step fm; finish

-- Tail d=1 b>=1: R5 R1 R2
theorem tail_d1_bpos : ⟨0, b + 1, 0, 1, e + 1⟩ [fm]⊢* ⟨2, b + 1, 0, 0, e⟩ := by
  step fm; step fm; step fm; finish

-- Phase 4: b drain with a>=1 (R3 R1 per round)
theorem b_drain : ∀ k, ⟨a + 1, k + 1, 0, 0, e⟩ [fm]⊢*
    ⟨a + k + 2, 0, 0, 0, e + 2 * k + 2⟩ := by
  intro k; induction' k with k ih generalizing a e
  · step fm; step fm; ring_nf; finish
  · rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]; step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (e := e + 2)); ring_nf; finish

-- Phase 4: b drain with a=0 (R5 R1 then b_drain)
theorem b_drain_zero : ∀ k, ⟨0, k + 1, 0, 0, e + 1⟩ [fm]⊢*
    ⟨k + 3, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing e
  · step fm; step fm; ring_nf; finish
  · step fm; step fm
    show ⟨3, k + 1, 0, 0, e⟩ [fm]⊢* _
    rw [show (3 : ℕ) = 2 + 1 from by ring]
    apply stepStar_trans (b_drain k (a := 2) (e := e)); ring_nf; finish

-- === Main case theorems ===

-- Case A = 3M+1: (3M+1, 0, 0, 0, E) ⊢⁺ (4M+2, 0, 0, 0, E+12M+3)
theorem case1 : ∀ M E, ⟨3 * M + 1, 0, 0, 0, E⟩ [fm]⊢⁺
    ⟨4 * M + 2, 0, 0, 0, E + 12 * M + 3⟩ := by
  intro M E
  rw [show 3 * M + 1 = 3 * M + 0 + 1 from by ring]; step fm
  show ⟨3 * M, 0, 1, 0, E + 2⟩ [fm]⊢* _
  rw [show 3 * M = 0 + 3 * M from by ring]
  apply stepStar_trans (r3_chain (3 * M) (a := 0) (c := 1) (e := E + 2))
  rw [show 1 + 3 * M = 0 + (3 * M + 1) from by ring]
  apply stepStar_trans (r4_chain (3 * M + 1) (c := 0) (d := 0) (e := E + 2 + 2 * (3 * M)))
  rw [show 0 + 2 * (3 * M + 1) = 3 * (2 * M) + 2 from by ring,
      show E + 2 + 2 * (3 * M) = (E + 4 * M + 2) + 2 * M from by ring]
  apply stepStar_trans (staircase_loop (2 * M) (b := 0) (r := 2) (e := E + 4 * M + 2))
  rw [show 0 + 2 * (2 * M) = 4 * M from by ring,
      show E + 4 * M + 2 = (E + 4 * M + 1) + 1 from by ring]
  rcases M with _ | M'
  · -- M=0: (0, 0, 0, 2, E+1) -> (1, 1, 0, 0, E) -> b_drain
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    apply stepStar_trans tail_d2_b0
    step fm; step fm; ring_nf; finish
  · -- M=M'+1: (0, 4M'+4, 0, 2, (E+4M'+5)+1)
    rw [show 4 * (M' + 1) = (4 * M' + 3) + 1 from by ring]
    apply stepStar_trans tail_d2_bpos
    -- Goal should have: (1, 4M'+3+2, 0, 0, E+4M'+1+4)
    -- Need to get to b_drain form: (0+1, (4M'+4)+1, 0, 0, ...)
    show ⟨1, 4 * M' + 3 + 2, 0, 0, E + (4 * M' + 1 + 4)⟩ [fm]⊢* _
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 4 * M' + 3 + 2 = (4 * M' + 4) + 1 from by ring,
        show E + (4 * M' + 1 + 4) = E + 4 * M' + 5 from by ring]
    apply stepStar_trans (b_drain (4 * M' + 4) (a := 0) (e := E + 4 * M' + 5))
    ring_nf; finish

-- Case A = 3M+2: (3M+2, 0, 0, 0, E) ⊢⁺ (4M+4, 0, 0, 0, E+12M+6)
theorem case2 : ∀ M E, ⟨3 * M + 2, 0, 0, 0, E⟩ [fm]⊢⁺
    ⟨4 * M + 4, 0, 0, 0, E + 12 * M + 6⟩ := by
  intro M E
  rw [show 3 * M + 2 = (3 * M + 1) + 1 from by ring]; step fm
  show ⟨3 * M + 1, 0, 1, 0, E + 2⟩ [fm]⊢* _
  rw [show 3 * M + 1 = 0 + (3 * M + 1) from by ring]
  apply stepStar_trans (r3_chain (3 * M + 1) (a := 0) (c := 1) (e := E + 2))
  rw [show 1 + (3 * M + 1) = 0 + (3 * M + 2) from by ring]
  apply stepStar_trans (r4_chain (3 * M + 2) (c := 0) (d := 0) (e := E + 2 + 2 * (3 * M + 1)))
  rw [show 0 + 2 * (3 * M + 2) = 3 * (2 * M + 1) + 1 from by ring,
      show E + 2 + 2 * (3 * M + 1) = (E + 4 * M + 3) + (2 * M + 1) from by ring]
  apply stepStar_trans (staircase_loop (2 * M + 1) (b := 0) (r := 1) (e := E + 4 * M + 3))
  rw [show 0 + 2 * (2 * M + 1) = 4 * M + 2 from by ring,
      show E + 4 * M + 3 = (E + 4 * M + 2) + 1 from by ring]
  rcases M with _ | M'
  · -- M=0: (0, 2, 0, 1, E+3)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
    apply stepStar_trans tail_d1_bpos
    show ⟨2, 0 + 1 + 1, 0, 0, E + 2⟩ [fm]⊢* _
    rw [show (2 : ℕ) = 1 + 1 from by ring, show 0 + 1 + 1 = 1 + 1 from by ring]
    apply stepStar_trans (b_drain 1 (a := 1) (e := E + 2))
    ring_nf; finish
  · -- M=M'+1: (0, 4M'+6, 0, 1, (E+4M'+7))
    rw [show 4 * (M' + 1) + 2 = (4 * M' + 5) + 1 from by ring]
    apply stepStar_trans tail_d1_bpos
    show ⟨2, 4 * M' + 5 + 1, 0, 0, E + 4 * (M' + 1) + 2⟩ [fm]⊢* _
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 4 * M' + 5 + 1 = (4 * M' + 5) + 1 from by ring,
        show E + 4 * (M' + 1) + 2 = E + 4 * M' + 6 from by ring]
    apply stepStar_trans (b_drain (4 * M' + 5) (a := 1) (e := E + 4 * M' + 6))
    ring_nf; finish

-- Case A = 3(M+1): (3(M+1), 0, 0, 0, E) ⊢⁺ (4M+6, 0, 0, 0, E+12M+9)
theorem case3 : ∀ M E, ⟨3 * (M + 1), 0, 0, 0, E⟩ [fm]⊢⁺
    ⟨4 * M + 6, 0, 0, 0, E + 12 * M + 9⟩ := by
  intro M E
  rw [show 3 * (M + 1) = (3 * M + 2) + 1 from by ring]; step fm
  show ⟨3 * M + 2, 0, 1, 0, E + 2⟩ [fm]⊢* _
  rw [show 3 * M + 2 = 0 + (3 * M + 2) from by ring]
  apply stepStar_trans (r3_chain (3 * M + 2) (a := 0) (c := 1) (e := E + 2))
  rw [show 1 + (3 * M + 2) = 0 + (3 * M + 3) from by ring]
  apply stepStar_trans (r4_chain (3 * M + 3) (c := 0) (d := 0) (e := E + 2 + 2 * (3 * M + 2)))
  rw [show 0 + 2 * (3 * M + 3) = 3 * (2 * M + 2) + 0 from by ring,
      show E + 2 + 2 * (3 * M + 2) = (E + 4 * M + 4) + (2 * M + 2) from by ring]
  apply stepStar_trans (staircase_loop (2 * M + 2) (b := 0) (r := 0) (e := E + 4 * M + 4))
  rw [show 0 + 2 * (2 * M + 2) = (4 * M + 3) + 1 from by ring,
      show E + 4 * M + 4 = (E + 4 * M + 3) + 1 from by ring]
  apply stepStar_trans (b_drain_zero (4 * M + 3) (e := E + 4 * M + 3))
  ring_nf; finish

-- Final nonhalt theorem
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩)
  · execute fm 8
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 2, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    obtain ⟨m, hm⟩ : ∃ m, a = 3 * m ∨ a = 3 * m + 1 ∨ a = 3 * m + 2 := by
      exact ⟨a / 3, by omega⟩
    rcases hm with rfl | rfl | rfl
    · -- a = 3m: A = 3m+2, use case2
      exact ⟨⟨4 * m + 4, 0, 0, 0, e + 12 * m + 6⟩,
        ⟨4 * m + 2, e + 12 * m + 6, by ring_nf⟩, case2 m e⟩
    · -- a = 3m+1: A = 3m+3 = 3(m+1), use case3
      refine ⟨⟨4 * m + 6, 0, 0, 0, e + 12 * m + 9⟩,
        ⟨4 * m + 4, e + 12 * m + 9, by ring_nf⟩, ?_⟩
      rw [show 3 * m + 1 + 2 = 3 * (m + 1) from by ring]
      exact case3 m e
    · -- a = 3m+2: A = 3m+4 = 3(m+1)+1, use case1(m+1)
      refine ⟨⟨4 * m + 6, 0, 0, 0, e + 12 * m + 15⟩,
        ⟨4 * m + 4, e + 12 * m + 15, by ring_nf⟩, ?_⟩
      rw [show 3 * m + 2 + 2 = 3 * (m + 1) + 1 from by ring,
          show e + 12 * m + 15 = e + 12 * (m + 1) + 3 from by ring]
      exact case1 (m + 1) e
  · exact ⟨0, 3, by ring_nf⟩

end Sz22_2003_unofficial_915
