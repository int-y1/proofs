import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #106: [7/15, 99/14, 2/3, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 1 -1  0  0  0
 0  0  1  0 -1
-1  1  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_106

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

-- R3 chain: b → a
theorem b_to_a : ∀ k a b, ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R4 chain: e → c
theorem e_to_c : ∀ k c e, ⟨a, 0, c, 0, e+k⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

-- R2-R1-R1 chain: 3 steps per round
theorem r2r1r1_chain : ∀ k a c d e, ⟨a+k, 0, c+2*k, d+1, e⟩ [fm]⊢* ⟨a, 0, c, d+1+k, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
  step fm
  step fm
  step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  apply stepStar_trans (ih a c (d + 1) (e + 1))
  ring_nf; finish

-- R3-R2 chain: 2 steps per round
theorem r3r2_chain : ∀ k b d e, ⟨0, b+1, 0, d+k, e⟩ [fm]⊢* ⟨0, b+1+k, 0, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  step fm
  apply stepStar_trans (ih (b + 1) d (e + 1))
  ring_nf; finish

-- Mixing phase
theorem to_r3r2_start (n : ℕ) : ⟨n+2, 0, 2*n+2, 0, 0⟩ [fm]⊢* ⟨0, 2, 0, n+1, n+3⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨n+1, 1, 2*n+2, 1, 1⟩)
  · step fm; finish
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨n+1, 0, 2*n+1, 2, 1⟩)
  · step fm; finish
  -- R2-R1-R1 chain: n rounds
  apply stepStar_trans (c₂ := ⟨1, 0, 1, n+2, n+1⟩)
  · have h := r2r1r1_chain n 1 1 1 1
    convert h using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨0, 2, 1, n+1, n+2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show n + 2 = (n + 1) + 1 from by ring]
    step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨0, 1, 0, n+2, n+2⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨1, 0, 0, n+2, n+2⟩)
  · step fm; finish
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show n + 2 = (n + 1) + 1 from by ring]
  step fm; ring_nf; finish

-- Main transition
theorem main_trans (n : ℕ) : ⟨n+2, 0, 2*n+2, 0, 0⟩ [fm]⊢⁺ ⟨n+3, 0, 2*n+4, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (to_r3r2_start n)
  -- R3-R2 chain
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, n+3, 0, 0, 2*n+4⟩)
  · have h := r3r2_chain (n + 1) 1 0 (n + 3)
    rw [show (1 : ℕ) + 1 = 2 from by ring,
        show 0 + (n + 1) = n + 1 from by ring,
        show 1 + 1 + (n + 1) = n + 3 from by ring,
        show n + 3 + (n + 1) = 2 * n + 4 from by ring] at h
    exact h
  -- R3 chain (b → a)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n+3, 0, 0, 0, 2*n+4⟩)
  · have h := b_to_a (e := 2 * n + 4) (n + 3) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R4 chain (e → c)
  apply step_stepStar_stepPlus (c₂ := ⟨n+3, 0, 1, 0, 2*n+3⟩)
  · show fm ⟨n + 3, 0, 0, 0, (2 * n + 3) + 1⟩ = some ⟨n + 3, 0, 1, 0, 2 * n + 3⟩
    simp [fm]
  · have h := e_to_c (a := n + 3) (2 * n + 3) 1 0
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 2, 0, 0⟩) (by execute fm 7)
  show ¬halts fm (0+2, 0, 2*0+2, 0, 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+2, 0, 2*n+2, 0, 0⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩
