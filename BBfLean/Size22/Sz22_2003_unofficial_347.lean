import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #347: [2/15, 1/154, 63/2, 121/3, 50/11]

Vector representation:
```
 1 -1 -1  0  0
-1  0  0 -1 -1
-1  2  0  1  0
 0 -1  0  0  2
 1  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_347

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- Rule 4 repeated: drain b into e
theorem b_to_e : ∀ k, ⟨(0 : ℕ), b+k, 0, d, 0⟩ [fm]⊢* ⟨0, b, 0, d, 2*k⟩ := by
  intro k; induction k generalizing b with
  | zero => exists 0
  | succ k ih =>
    rw [show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 1))
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; finish

-- Alternating rules 5 and 2: drain d,e into c
theorem de_to_c : ∀ k, ⟨(0 : ℕ), 0, c, d+k, e+2*k⟩ [fm]⊢* ⟨0, 0, c+2*k, d, e⟩ := by
  intro k; induction k generalizing c d e with
  | zero => exists 0
  | succ k ih =>
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c := c + 2) (d := d) (e := e))
    ring_nf; finish

-- Consume c by 2 each round: 3 steps
theorem consume_c_one : ⟨a+1, 0, c+2, d, 0⟩ [fm]⊢* ⟨a+2, 0, c, d+1, 0⟩ := by
  step fm; step fm; step fm; finish

-- Consume c repeated
theorem consume_c : ∀ k, ⟨a+1, (0 : ℕ), 2*k, a, 0⟩ [fm]⊢* ⟨a+k+1, 0, 0, a+k, 0⟩ := by
  intro k; induction k generalizing a with
  | zero => exists 0
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans (@consume_c_one a (2*k) a)
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

-- Rule 3 repeated: drain a into b and d
theorem a_to_bd : ∀ k, ⟨a+k, b, (0 : ℕ), d, 0⟩ [fm]⊢* ⟨a, b+2*k, 0, d+k, 0⟩ := by
  intro k; induction k generalizing a b d with
  | zero => exists 0
  | succ k ih =>
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (b := b + 2) (d := d + 1))
    ring_nf; finish

-- Main cycle: (0, 2*(n+1), 0, 2*n+1, 0) →⁺ (0, 4*(n+1), 0, 4*n+3, 0)
theorem cycle (n : ℕ) : ⟨0, 2*(n+1), 0, 2*n+1, 0⟩ [fm]⊢⁺ ⟨0, 4*(n+1), 0, 4*n+3, 0⟩ := by
  -- Phase A: drain b to e
  have hA : ⟨(0 : ℕ), 2*(n+1), 0, 2*n+1, 0⟩ [fm]⊢* ⟨0, 0, 0, 2*n+1, 4*(n+1)⟩ := by
    rw [show 2*(n+1) = 0 + 2*(n+1) from by ring,
        show 4*(n+1) = 2*(2*(n+1)) from by ring]
    exact b_to_e (2*(n+1)) (b := 0)
  -- Phase B: drain d,e into c
  have hB : ⟨(0 : ℕ), 0, 0, 2*n+1, 4*(n+1)⟩ [fm]⊢* ⟨0, 0, 4*n+2, 0, 2⟩ := by
    rw [show (2*n+1 : ℕ) = 0 + (2*n+1) from by ring,
        show 4*(n+1) = 2 + 2*(2*n+1) from by ring,
        show 4*n+2 = 0 + 2*(2*n+1) from by ring]
    exact de_to_c (2*n+1) (c := 0) (d := 0) (e := 2)
  -- Phase B': rule 5 once, then Phase C: 4 fixed steps
  have hBC : ⟨(0 : ℕ), 0, 4*n+2, 0, 2⟩ [fm]⊢⁺ ⟨1, 0, 4*n+2, 0, 0⟩ := by
    step fm; step fm; step fm; step fm; step fm; finish
  -- Phase D: consume c
  have hD : ⟨(1 : ℕ), 0, 4*n+2, 0, 0⟩ [fm]⊢* ⟨2*n+2, 0, 0, 2*n+1, 0⟩ := by
    rw [show (4*n+2 : ℕ) = 2*(2*n+1) from by ring]
    have h := @consume_c 0 (2*n+1)
    simp only [Nat.zero_add] at h
    rw [show 2 * n + 1 + 1 = 2 * n + 2 from by ring] at h
    exact h
  -- Phase E: drain a to b,d
  have hE : ⟨2*n+2, (0 : ℕ), 0, 2*n+1, 0⟩ [fm]⊢* ⟨0, 4*(n+1), 0, 4*n+3, 0⟩ := by
    rw [show (2*n+2 : ℕ) = 0 + (2*n+2) from by ring,
        show 4*(n+1) = 0 + 2*(2*n+2) from by ring,
        show 4*n+3 = (2*n+1) + (2*n+2) from by ring]
    exact @a_to_bd 0 0 (2*n+1) (2*n+2)
  exact stepStar_stepPlus_stepPlus hA
    (stepStar_stepPlus_stepPlus hB
      (stepPlus_stepStar_stepPlus hBC
        (stepStar_trans hD hE)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 1, 0⟩)
  · execute fm 1
  · apply progress_nonhalt_simple
      (fun n => (⟨0, 2*(n+1), 0, 2*n+1, 0⟩ : Q))
      0
    intro i
    refine ⟨2*i+1, ?_⟩
    have h := cycle i
    rw [show 2*((2*i+1)+1) = 4*(i+1) from by ring,
        show 2*(2*i+1)+1 = 4*i+3 from by ring]
    exact h

end Sz22_2003_unofficial_347
