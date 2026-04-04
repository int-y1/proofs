import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1860: [9/35, 22/5, 125/33, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  0
 1  0 -1  0  1
 0 -1  3  0 -1
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1860

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+3, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 chain: (a, 0, 0, d, e+k) ⊢* (a, 0, 0, d+k, e)
theorem e_to_d : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) e); ring_nf; finish

-- R3+R2x3 loop: b rounds, each a+=3, e+=2
theorem r3r2_loop : ∀ k, ∀ a e, ⟨a, k, 0, 0, e + 1⟩ [fm]⊢* ⟨a + 3 * k, 0, 0, 0, e + 1 + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; exists 0
  · step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (e + 2)); ring_nf; finish

-- One drain round: R5+R1+R3+R1x3 (6 steps)
theorem drain_round : ⟨a + 1, b, 0, d + 4, 0⟩ [fm]⊢* ⟨a, b + 7, 0, d, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- Multiple drain rounds
theorem drain_loop : ∀ k, ∀ a b d, ⟨a + k, b, 0, d + 4 * k, 0⟩ [fm]⊢* ⟨a, b + 7 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring,
        show d + 4 * (k + 1) = (d + 4 * k) + 4 from by ring]
    apply stepStar_trans drain_round
    apply stepStar_trans (ih a (b + 7) d); ring_nf; finish

-- Full drain d=4k+2: (a+k+1, 0, 0, 4*k+2, 0) ⊢⁺ (a+21*k+11, 0, 0, 0, 14*k+8)
theorem full_d4k2 : ⟨a + k + 1, 0, 0, 4 * k + 2, 0⟩ [fm]⊢⁺ ⟨a + 21 * k + 11, 0, 0, 0, 14 * k + 8⟩ := by
  rw [show a + k + 1 = (a + 1) + k from by ring,
      show 4 * k + 2 = 2 + 4 * k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop k (a + 1) 0 2)
  rw [show 0 + 7 * k = 7 * k from by ring]
  -- now at (a+1, 7k, 0, 2, 0). R5 fires as first step.
  step fm  -- R5: (a, 7k, 1, 2, 1)
  step fm  -- R1: (a, 7k+2, 0, 1, 1)
  step fm  -- R3: (a, 7k+1, 3, 1, 0)
  step fm  -- R1: (a, 7k+3, 2, 0, 0)
  step fm  -- R2: (a+1, 7k+3, 1, 0, 1)
  step fm  -- R2: (a+2, 7k+3, 0, 0, 2)
  -- now at (a+2, 7k+3, 0, 0, 2). r3r2_loop (7k+3) rounds.
  apply stepStar_trans (r3r2_loop (7 * k + 3) (a + 2) 1)
  ring_nf; finish

-- Full drain d=4k+3: (a+k+1, 0, 0, 4*k+3, 0) ⊢⁺ (a+21*k+16, 0, 0, 0, 14*k+11)
theorem full_d4k3 : ⟨a + k + 1, 0, 0, 4 * k + 3, 0⟩ [fm]⊢⁺ ⟨a + 21 * k + 16, 0, 0, 0, 14 * k + 11⟩ := by
  rw [show a + k + 1 = (a + 1) + k from by ring,
      show 4 * k + 3 = 3 + 4 * k from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop k (a + 1) 0 3)
  rw [show 0 + 7 * k = 7 * k from by ring]
  -- now at (a+1, 7k, 0, 3, 0). d3 exit: R5+R1+R3+R1x2+R2
  step fm; step fm; step fm; step fm; step fm; step fm
  -- now at (a+1, 7k+5, 0, 0, 1). r3r2_loop (7k+5) rounds.
  apply stepStar_trans (r3r2_loop (7 * k + 5) (a + 1) 0)
  ring_nf; finish

-- Full drain d=4(k+1): (a+k+2, 0, 0, 4*(k+1), 0) ⊢⁺ (a+21*k+22, 0, 0, 0, 14*k+16)
theorem full_d4k0 : ⟨a + k + 2, 0, 0, 4 * (k + 1), 0⟩ [fm]⊢⁺ ⟨a + 21 * k + 22, 0, 0, 0, 14 * k + 16⟩ := by
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring,
      show 4 * (k + 1) = 0 + 4 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop (k + 1) (a + 1) 0 0)
  rw [show 0 + 7 * (k + 1) = 7 * k + 7 from by ring]
  -- now at (a+1, 7k+7, 0, 0, 0). d0 exit: R5+R2
  step fm; step fm
  -- now at (a+1, 7k+7, 0, 0, 2). r3r2_loop (7k+7) rounds.
  apply stepStar_trans (r3r2_loop (7 * k + 7) (a + 1) 1)
  ring_nf; finish

-- Full drain d=4(k+1)+1: (a+k+2, 0, 0, 4*(k+1)+1, 0) ⊢⁺ (a+21*k+27, 0, 0, 0, 14*k+19)
theorem full_d4k1 : ⟨a + k + 2, 0, 0, 4 * (k + 1) + 1, 0⟩ [fm]⊢⁺ ⟨a + 21 * k + 27, 0, 0, 0, 14 * k + 19⟩ := by
  rw [show a + k + 2 = (a + 1) + (k + 1) from by ring,
      show 4 * (k + 1) + 1 = 1 + 4 * (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop (k + 1) (a + 1) 0 1)
  rw [show 0 + 7 * (k + 1) = 7 * k + 7 from by ring]
  -- now at (a+1, 7k+7, 0, 1, 0). d1 exit: R5+R1+R3+R2x3
  step fm; step fm; step fm; step fm; step fm; step fm
  -- now at (a+3, 7k+8, 0, 0, 3). r3r2_loop (7k+8) rounds.
  apply stepStar_trans (r3r2_loop (7 * k + 8) (a + 3) 2)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨11, 0, 0, 0, 8⟩) (by execute fm 22)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e + 2⟩ ∧ 4 * a ≥ e + 6)
  · intro c ⟨a, e, hq, hinv⟩; subst hq
    obtain ⟨k, rfl | rfl | rfl | rfl⟩ : ∃ k, e = 4 * k ∨ e = 4 * k + 1 ∨ e = 4 * k + 2 ∨ e = 4 * k + 3 :=
      ⟨e / 4, by omega⟩
    · -- e = 4k, d = e+2 = 4k+2
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      refine ⟨⟨m + 21 * k + 11, 0, 0, 0, 14 * k + 8⟩,
        ⟨m + 21 * k + 11, 14 * k + 6, rfl, by omega⟩, ?_⟩
      apply stepStar_stepPlus_stepPlus
      · rw [show 4 * k + 2 = 0 + (4 * k + 2) from by ring]
        exact e_to_d (4 * k + 2) (m + k + 1) 0 0
      rw [show 0 + (4 * k + 2) = 4 * k + 2 from by ring]
      exact full_d4k2
    · -- e = 4k+1, d = e+2 = 4k+3
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      refine ⟨⟨m + 21 * k + 16, 0, 0, 0, 14 * k + 11⟩,
        ⟨m + 21 * k + 16, 14 * k + 9, rfl, by omega⟩, ?_⟩
      apply stepStar_stepPlus_stepPlus
      · rw [show 4 * k + 3 = 0 + (4 * k + 3) from by ring]
        exact e_to_d (4 * k + 3) (m + k + 1) 0 0
      rw [show 0 + (4 * k + 3) = 4 * k + 3 from by ring]
      exact full_d4k3
    · -- e = 4k+2, d = e+2 = 4(k+1)
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      refine ⟨⟨m + 21 * k + 22, 0, 0, 0, 14 * k + 16⟩,
        ⟨m + 21 * k + 22, 14 * k + 14, rfl, by omega⟩, ?_⟩
      apply stepStar_stepPlus_stepPlus
      · rw [show 4 * k + 4 = 0 + (4 * k + 4) from by ring]
        exact e_to_d (4 * k + 4) (m + k + 2) 0 0
      rw [show 0 + (4 * k + 4) = 4 * (k + 1) from by ring]
      exact full_d4k0
    · -- e = 4k+3, d = e+2 = 4(k+1)+1
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 2 := ⟨a - k - 2, by omega⟩
      refine ⟨⟨m + 21 * k + 27, 0, 0, 0, 14 * k + 19⟩,
        ⟨m + 21 * k + 27, 14 * k + 17, rfl, by omega⟩, ?_⟩
      apply stepStar_stepPlus_stepPlus
      · rw [show 4 * k + 5 = 0 + (4 * k + 5) from by ring]
        exact e_to_d (4 * k + 5) (m + k + 2) 0 0
      rw [show 0 + (4 * k + 5) = 4 * (k + 1) + 1 from by ring]
      exact full_d4k1
  · exact ⟨11, 6, rfl, by omega⟩
