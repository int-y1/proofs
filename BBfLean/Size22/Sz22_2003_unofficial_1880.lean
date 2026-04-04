import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1880: [9/35, 5/33, 242/5, 7/11, 75/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1  0 -1  0  2
 0  0  0  1 -1
-1  1  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1880

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k a e, ⟨a, 0, k + 1, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + 2 * (k + 1)⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; finish
  · step fm
    apply stepStar_trans (ih (a + 1) (e + 2))
    ring_nf; finish

theorem drain : ∀ k a b d, ⟨a + k, b, 0, d + 2 * k, 0⟩ [fm]⊢* ⟨a, b + 5 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (a + 1) b (d + 2))
    step fm; step fm; step fm
    ring_nf; finish

theorem d1_end : ⟨a + 1, b, 0, 1, 0⟩ [fm]⊢* ⟨a + 1, b + 1, 2, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem d0_end : ⟨a + 1, b, 0, 0, 0⟩ [fm]⊢* ⟨a, b + 1, 2, 0, 0⟩ := by
  step fm; finish

theorem r3r2r2_loop : ∀ n a c, ⟨a, b + 2 * n, c + 1, 0, 0⟩ [fm]⊢* ⟨a + n, b, c + n + 1, 0, 0⟩ := by
  intro n; induction' n with n ih <;> intro a c
  · exists 0
  · rw [show b + 2 * (n + 1) = b + 2 * n + 2 from by ring]
    step fm; step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (c + 1))
    ring_nf; finish

theorem b1_tail : ⟨a, 1, c + 1, 0, 0⟩ [fm]⊢* ⟨a + 1, 0, c + 1, 0, 1⟩ := by
  step fm; step fm; finish

-- Odd d full transition: drain to d=1, then d1_end, then odd_b middle, then e_to_d.
-- (a+k+1, 0, 0, 2*k+1, 0) →* (a+1, 5*k, 0, 1, 0) →* (a+1, 5*k+1, 2, 0, 0) →* ...
-- For k even (k=2j): b=10j+1 (odd, n=5j), result = (a+10j+4, 0, 0, 10j+5, 0)
-- For k odd (k=2j+1): b=10j+6 (even, n=5j+3), result = (a+10j+9, 0, 0, 10j+10, 0)

-- Full transition for d=4j+1 (k=2j)
theorem trans_full_d4j1 :
    ⟨a + 2 * j + 1, 0, 0, 4 * j + 1, 0⟩ [fm]⊢* ⟨a + 10 * j + 4, 0, 0, 10 * j + 5, 0⟩ := by
  -- drain 2j rounds: (a+1, 10j, 0, 1, 0)
  rw [show a + 2 * j + 1 = (a + 1) + 2 * j from by ring,
      show 4 * j + 1 = 1 + 2 * (2 * j) from by ring]
  apply stepStar_trans (drain (2 * j) (a + 1) 0 1)
  rw [show 0 + 5 * (2 * j) = 10 * j from by ring]
  -- d1_end: (a+1, 10j+1, 2, 0, 0)
  apply stepStar_trans (d1_end (a := a) (b := 10 * j))
  -- R3R2R2 with b=10j+1 (odd): 5j rounds, then b1_tail
  rw [show 10 * j + 1 = 1 + 2 * (5 * j) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_loop (5 * j) (a + 1) 1 (b := 1))
  rw [show 1 + 5 * j + 1 = (5 * j + 1) + 1 from by ring]
  apply stepStar_trans (b1_tail (a := a + 1 + 5 * j) (c := 5 * j + 1))
  rw [show 5 * j + 1 + 1 = (5 * j + 1) + 1 from by ring]
  -- R3 chain
  apply stepStar_trans (r3_chain (5 * j + 1) (a + 1 + 5 * j + 1) 1)
  -- e_to_d
  show ⟨a + 1 + 5 * j + 1 + (5 * j + 1) + 1, 0, 0, 0, 1 + 2 * (5 * j + 1 + 1)⟩ [fm]⊢*
       ⟨a + 10 * j + 4, 0, 0, 10 * j + 5, 0⟩
  rw [show a + 1 + 5 * j + 1 + (5 * j + 1) + 1 = a + 10 * j + 4 from by ring,
      show 1 + 2 * (5 * j + 1 + 1) = 10 * j + 5 from by ring]
  apply stepStar_trans (e_to_d (10 * j + 5) 0)
  ring_nf; finish

-- Full transition for d=4j+3 (k=2j+1)
theorem trans_full_d4j3 :
    ⟨a + 2 * j + 2, 0, 0, 4 * j + 3, 0⟩ [fm]⊢* ⟨a + 10 * j + 9, 0, 0, 10 * j + 10, 0⟩ := by
  rw [show a + 2 * j + 2 = (a + 1) + (2 * j + 1) from by ring,
      show 4 * j + 3 = 1 + 2 * (2 * j + 1) from by ring]
  apply stepStar_trans (drain (2 * j + 1) (a + 1) 0 1)
  rw [show 0 + 5 * (2 * j + 1) = 10 * j + 5 from by ring]
  apply stepStar_trans (d1_end (a := a) (b := 10 * j + 5))
  rw [show 10 * j + 5 + 1 = 0 + 2 * (5 * j + 3) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_loop (5 * j + 3) (a + 1) 1 (b := 0))
  rw [show 1 + (5 * j + 3) + 1 = (5 * j + 4) + 1 from by ring]
  apply stepStar_trans (r3_chain (5 * j + 4) (a + 1 + (5 * j + 3)) 0)
  show ⟨a + 1 + (5 * j + 3) + (5 * j + 4) + 1, 0, 0, 0, 0 + 2 * (5 * j + 4 + 1)⟩ [fm]⊢*
       ⟨a + 10 * j + 9, 0, 0, 10 * j + 10, 0⟩
  rw [show a + 1 + (5 * j + 3) + (5 * j + 4) + 1 = a + 10 * j + 9 from by ring,
      show 0 + 2 * (5 * j + 4 + 1) = 10 * j + 10 from by ring]
  apply stepStar_trans (e_to_d (10 * j + 10) 0)
  ring_nf; finish

-- Even d full transition: drain to d=0, then d0_end, then middle phase.
-- (a+k+1, 0, 0, 2*(k+1), 0) →* (a+1, 5*(k+1), 0, 0, 0) →* (a, 5*(k+1)+1, 2, 0, 0) →* ...
-- For k+1 even (k=2j+1, so k+1=2j+2): b=10j+11 (odd, n=5j+5)
-- For k+1 odd (k=2j, so k+1=2j+1): b=10j+6 (even, n=5j+3)

-- Full transition for d=4j+2 (k+1 = 2j+1, k=2j)
theorem trans_full_d4j2 :
    ⟨a + 2 * j + 2, 0, 0, 4 * j + 2, 0⟩ [fm]⊢* ⟨a + 10 * j + 8, 0, 0, 10 * j + 10, 0⟩ := by
  rw [show a + 2 * j + 2 = (a + 1) + (2 * j + 1) from by ring,
      show 4 * j + 2 = 0 + 2 * (2 * j + 1) from by ring]
  apply stepStar_trans (drain (2 * j + 1) (a + 1) 0 0)
  rw [show 0 + 5 * (2 * j + 1) = 10 * j + 5 from by ring]
  apply stepStar_trans (d0_end (a := a) (b := 10 * j + 5))
  rw [show 10 * j + 5 + 1 = 0 + 2 * (5 * j + 3) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_loop (5 * j + 3) a 1 (b := 0))
  rw [show 1 + (5 * j + 3) + 1 = (5 * j + 4) + 1 from by ring]
  apply stepStar_trans (r3_chain (5 * j + 4) (a + (5 * j + 3)) 0)
  show ⟨a + (5 * j + 3) + (5 * j + 4) + 1, 0, 0, 0, 0 + 2 * (5 * j + 4 + 1)⟩ [fm]⊢*
       ⟨a + 10 * j + 8, 0, 0, 10 * j + 10, 0⟩
  rw [show a + (5 * j + 3) + (5 * j + 4) + 1 = a + 10 * j + 8 from by ring,
      show 0 + 2 * (5 * j + 4 + 1) = 10 * j + 10 from by ring]
  apply stepStar_trans (e_to_d (10 * j + 10) 0)
  ring_nf; finish

-- Full transition for d=4(j+1) (k+1 = 2j+2, k=2j+1)
theorem trans_full_d4j4 :
    ⟨a + 2 * j + 3, 0, 0, 4 * (j + 1), 0⟩ [fm]⊢* ⟨a + 10 * j + 13, 0, 0, 10 * j + 15, 0⟩ := by
  rw [show a + 2 * j + 3 = (a + 1) + (2 * j + 2) from by ring,
      show 4 * (j + 1) = 0 + 2 * (2 * j + 2) from by ring]
  apply stepStar_trans (drain (2 * j + 2) (a + 1) 0 0)
  rw [show 0 + 5 * (2 * j + 2) = 10 * j + 10 from by ring]
  apply stepStar_trans (d0_end (a := a) (b := 10 * j + 10))
  rw [show 10 * j + 10 + 1 = 1 + 2 * (5 * j + 5) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_loop (5 * j + 5) a 1 (b := 1))
  rw [show 1 + (5 * j + 5) + 1 = (5 * j + 6) + 1 from by ring]
  apply stepStar_trans (b1_tail (a := a + (5 * j + 5)) (c := 5 * j + 6))
  rw [show 5 * j + 6 + 1 = (5 * j + 6) + 1 from by ring]
  apply stepStar_trans (r3_chain (5 * j + 6) (a + (5 * j + 5) + 1) 1)
  show ⟨a + (5 * j + 5) + 1 + (5 * j + 6) + 1, 0, 0, 0, 1 + 2 * (5 * j + 6 + 1)⟩ [fm]⊢*
       ⟨a + 10 * j + 13, 0, 0, 10 * j + 15, 0⟩
  rw [show a + (5 * j + 5) + 1 + (5 * j + 6) + 1 = a + 10 * j + 13 from by ring,
      show 1 + 2 * (5 * j + 6 + 1) = 10 * j + 15 from by ring]
  apply stepStar_trans (e_to_d (10 * j + 15) 0)
  ring_nf; finish

-- Convert ⊢* to ⊢⁺ (the start and end states are different)
theorem trans_d4j1 : ⟨a + 2 * j + 1, 0, 0, 4 * j + 1, 0⟩ [fm]⊢⁺ ⟨a + 10 * j + 4, 0, 0, 10 * j + 5, 0⟩ := by
  apply stepStar_stepPlus trans_full_d4j1
  intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.1) h; simp at this; omega

theorem trans_d4j3 : ⟨a + 2 * j + 2, 0, 0, 4 * j + 3, 0⟩ [fm]⊢⁺ ⟨a + 10 * j + 9, 0, 0, 10 * j + 10, 0⟩ := by
  apply stepStar_stepPlus trans_full_d4j3
  intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.1) h; simp at this; omega

theorem trans_d4j2 : ⟨a + 2 * j + 2, 0, 0, 4 * j + 2, 0⟩ [fm]⊢⁺ ⟨a + 10 * j + 8, 0, 0, 10 * j + 10, 0⟩ := by
  apply stepStar_stepPlus trans_full_d4j2
  intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.1) h; simp at this; omega

theorem trans_d4j4 : ⟨a + 2 * j + 3, 0, 0, 4 * (j + 1), 0⟩ [fm]⊢⁺ ⟨a + 10 * j + 13, 0, 0, 10 * j + 15, 0⟩ := by
  apply stepStar_stepPlus trans_full_d4j4
  intro h; have := congr_arg (fun q : Q ↦ q.2.2.2.1) h; simp at this; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 5, 0⟩)
  · execute fm 10
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ 2 * a ≥ d + 1)
  · intro c ⟨a, d, hq, hd, ha⟩; subst hq
    obtain ⟨j, rfl | rfl | rfl | rfl⟩ : ∃ j, d = 4 * j + 1 ∨ d = 4 * j + 2 ∨ d = 4 * j + 3 ∨ d = 4 * (j + 1) :=
      ⟨(d - 1) / 4, by omega⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + (2 * j + 1) := ⟨a - (2 * j + 1), by omega⟩
      exact ⟨⟨m + 10 * j + 4, 0, 0, 10 * j + 5, 0⟩,
        ⟨m + 10 * j + 4, 10 * j + 5, rfl, by omega, by omega⟩, trans_d4j1⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + (2 * j + 2) := ⟨a - (2 * j + 2), by omega⟩
      exact ⟨⟨m + 10 * j + 8, 0, 0, 10 * j + 10, 0⟩,
        ⟨m + 10 * j + 8, 10 * j + 10, rfl, by omega, by omega⟩, trans_d4j2⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + (2 * j + 2) := ⟨a - (2 * j + 2), by omega⟩
      exact ⟨⟨m + 10 * j + 9, 0, 0, 10 * j + 10, 0⟩,
        ⟨m + 10 * j + 9, 10 * j + 10, rfl, by omega, by omega⟩, trans_d4j3⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + (2 * j + 3) := ⟨a - (2 * j + 3), by omega⟩
      exact ⟨⟨m + 10 * j + 13, 0, 0, 10 * j + 15, 0⟩,
        ⟨m + 10 * j + 13, 10 * j + 15, rfl, by omega, by omega⟩, trans_d4j4⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩
