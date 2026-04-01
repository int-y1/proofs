import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1446: [7/15, 242/3, 9/77, 5/11, 99/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  2  0 -1 -1
 0  0  1  0 -1
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1446

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- R4 chain: transfer e to c (when b=0, d=0)
theorem e_to_c : ∀ k, ∀ c e, (⟨a, 0, c, 0, e + k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- Phase 2 round: R5-R1-R1-R3-R1-R1 (6 steps)
theorem phase2_round : ∀ a c d, (⟨a + 1, 0, c + 4, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, c, d + 3, 0⟩ := by
  intro a c d
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Phase 2 chain: k rounds
theorem phase2_chain : ∀ k, ∀ a c d,
    (⟨a + k, 0, c + 4 * k, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; finish
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring]
    apply stepStar_trans (phase2_round (a + k) (c + 4 * k) d)
    apply stepStar_trans (ih a c (d + 3))
    ring_nf; finish

-- c=0 terminal: R5-R2-R2 (3 steps)
theorem c0_term : ∀ a d,
    (⟨a + 1, 0, 0, d, 0⟩ : Q) [fm]⊢* ⟨a + 2, 0, 0, d, 5⟩ := by
  intro a d; step fm; step fm; step fm; ring_nf; finish

-- c=1 terminal: R5-R1-R2 (3 steps)
theorem c1_term : ∀ a d,
    (⟨a + 1, 0, 1, d, 0⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, d + 1, 3⟩ := by
  intro a d; step fm; step fm; step fm; ring_nf; finish

-- c=2 terminal: R5-R1-R1-R3-R2-R2 (6 steps)
theorem c2_term : ∀ a d,
    (⟨a + 1, 0, 2, d, 0⟩ : Q) [fm]⊢* ⟨a + 2, 0, 0, d + 1, 4⟩ := by
  intro a d
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- c=3 terminal: R5-R1-R1-R3-R1-R2 (6 steps)
theorem c3_term : ∀ a d,
    (⟨a + 1, 0, 3, d, 0⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, d + 2, 2⟩ := by
  intro a d
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Micro-step: R3-R2-R2 (3 steps)
theorem micro_step (a d e : ℕ) :
    (⟨a, 0, 0, d + 1, e + 1⟩ : Q) [fm]⊢⁺ ⟨a + 2, 0, 0, d, e + 4⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

-- Full cycle e%4=0
theorem full_cycle_r0 (a k : ℕ) :
    (⟨a + k, 0, 0, 1, 4 * k + 1⟩ : Q) [fm]⊢⁺ ⟨a + 2, 0, 0, 3 * k + 3, 5⟩ := by
  apply stepPlus_stepStar_stepPlus (micro_step (a + k) 0 (4 * k))
  rw [show (4 * k + 4 : ℕ) = 0 + (4 * k + 4) from by ring]
  apply stepStar_trans (e_to_c (4 * k + 4) 0 0 (a := a + k + 2))
  rw [show (0 + (4 * k + 4) : ℕ) = 0 + 4 * (k + 1) from by ring,
      show a + k + 2 = (a + 1) + (k + 1) from by ring]
  apply stepStar_trans (phase2_chain (k + 1) (a + 1) 0 0)
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
  apply stepStar_trans (c0_term a (3 * k + 3))
  ring_nf; finish

-- Full cycle e%4=1
theorem full_cycle_r1 (a k : ℕ) :
    (⟨a + k, 0, 0, 1, 4 * k + 2⟩ : Q) [fm]⊢⁺ ⟨a + 1, 0, 0, 3 * k + 4, 3⟩ := by
  apply stepPlus_stepStar_stepPlus (micro_step (a + k) 0 (4 * k + 1))
  rw [show (4 * k + 1 + 4 : ℕ) = 0 + (4 * k + 5) from by ring]
  apply stepStar_trans (e_to_c (4 * k + 5) 0 0 (a := a + k + 2))
  rw [show (0 + (4 * k + 5) : ℕ) = 1 + 4 * (k + 1) from by ring,
      show a + k + 2 = (a + 1) + (k + 1) from by ring]
  apply stepStar_trans (phase2_chain (k + 1) (a + 1) 1 0)
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
  apply stepStar_trans (c1_term a (3 * k + 3))
  ring_nf; finish

-- Full cycle e%4=2
theorem full_cycle_r2 (a k : ℕ) :
    (⟨a + k, 0, 0, 1, 4 * k + 3⟩ : Q) [fm]⊢⁺ ⟨a + 2, 0, 0, 3 * k + 4, 4⟩ := by
  apply stepPlus_stepStar_stepPlus (micro_step (a + k) 0 (4 * k + 2))
  rw [show (4 * k + 2 + 4 : ℕ) = 0 + (4 * k + 6) from by ring]
  apply stepStar_trans (e_to_c (4 * k + 6) 0 0 (a := a + k + 2))
  rw [show (0 + (4 * k + 6) : ℕ) = 2 + 4 * (k + 1) from by ring,
      show a + k + 2 = (a + 1) + (k + 1) from by ring]
  apply stepStar_trans (phase2_chain (k + 1) (a + 1) 2 0)
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
  apply stepStar_trans (c2_term a (3 * k + 3))
  ring_nf; finish

-- Full cycle e%4=3
theorem full_cycle_r3 (a k : ℕ) :
    (⟨a + k, 0, 0, 1, 4 * k + 4⟩ : Q) [fm]⊢⁺ ⟨a + 1, 0, 0, 3 * k + 5, 2⟩ := by
  apply stepPlus_stepStar_stepPlus (micro_step (a + k) 0 (4 * k + 3))
  rw [show (4 * k + 3 + 4 : ℕ) = 0 + (4 * k + 7) from by ring]
  apply stepStar_trans (e_to_c (4 * k + 7) 0 0 (a := a + k + 2))
  rw [show (0 + (4 * k + 7) : ℕ) = 3 + 4 * (k + 1) from by ring,
      show a + k + 2 = (a + 1) + (k + 1) from by ring]
  apply stepStar_trans (phase2_chain (k + 1) (a + 1) 3 0)
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring]
  apply stepStar_trans (c3_term a (3 * k + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 4, 3⟩) (by execute fm 17)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d e, q = ⟨a, 0, 0, d + 1, e + 1⟩ ∧ 4 * a ≥ e)
  · intro q ⟨a, d, e, hq, hae⟩; subst hq
    rcases d with _ | d
    · -- d = 0: full cycle case
      have h4 : e % 4 < 4 := Nat.mod_lt _ (by omega)
      obtain ⟨k, hk⟩ : ∃ k, e = 4 * k + e % 4 := ⟨e / 4, by omega⟩
      interval_cases (e % 4)
      · -- e%4=0
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + k := ⟨a - k, by omega⟩
        refine ⟨⟨a' + 2, 0, 0, 3 * k + 3, 5⟩,
          ⟨a' + 2, 3 * k + 2, 4, by ring_nf, by omega⟩, ?_⟩
        have he : e = 4 * k := by omega
        rw [he]; exact full_cycle_r0 a' k
      · -- e%4=1
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + k := ⟨a - k, by omega⟩
        refine ⟨⟨a' + 1, 0, 0, 3 * k + 4, 3⟩,
          ⟨a' + 1, 3 * k + 3, 2, by ring_nf, by omega⟩, ?_⟩
        have he : e = 4 * k + 1 := by omega
        rw [he]; exact full_cycle_r1 a' k
      · -- e%4=2
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + k := ⟨a - k, by omega⟩
        refine ⟨⟨a' + 2, 0, 0, 3 * k + 4, 4⟩,
          ⟨a' + 2, 3 * k + 3, 3, by ring_nf, by omega⟩, ?_⟩
        have he : e = 4 * k + 2 := by omega
        rw [he]; exact full_cycle_r2 a' k
      · -- e%4=3
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + k := ⟨a - k, by omega⟩
        refine ⟨⟨a' + 1, 0, 0, 3 * k + 5, 2⟩,
          ⟨a' + 1, 3 * k + 4, 1, by ring_nf, by omega⟩, ?_⟩
        have he : e = 4 * k + 3 := by omega
        rw [he]; exact full_cycle_r3 a' k
    · -- d ≥ 1: micro-step
      exact ⟨⟨a + 2, 0, 0, d + 1, e + 4⟩,
        ⟨a + 2, d, e + 3, by ring_nf, by omega⟩,
        micro_step a (d + 1) e⟩
  · exact ⟨1, 3, 2, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1446
