import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #16: [18/35, 1/363, 5/3, 11/5, 147/2]

Vector representation:
```
 1  2 -1 -1  0
 0 -1  0  0 -2
 0 -1  1  0  0
 0  0 -1  0  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_16

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R3 repeated: b → c (e=0)
theorem b_to_c_e0 : ∀ k, ∀ b c, ⟨a, b+k, c, 0, 0⟩ [fm]⊢* ⟨a, b, c+k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro b c
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 repeated: b → c (e=1)
theorem b_to_c_e1 : ∀ k, ∀ b c, ⟨a, b+k, c, 0, 1⟩ [fm]⊢* ⟨a, b, c+k, 0, 1⟩ := by
  intro k; induction' k with k h <;> intro b c
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4 repeated: c → e
theorem c_to_e : ∀ k, ∀ c e, ⟨a, 0, c+k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1+R3 chain (e=0)
theorem r1r3_chain_e0 : ∀ k, ∀ A B, ⟨A, B, 1, k+1, 0⟩ [fm]⊢* ⟨A+k+1, B+k+2, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B
  · step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm
    step fm
    have h := ih (A + 1) (B + 1)
    apply stepStar_trans h
    ring_nf; finish

-- R1+R3 chain (e=1)
theorem r1r3_chain_e1 : ∀ k, ∀ A B, ⟨A, B, 1, k+1, 1⟩ [fm]⊢* ⟨A+k+1, B+k+2, 0, 0, 1⟩ := by
  intro k; induction' k with k ih <;> intro A B
  · step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm
    step fm
    have h := ih (A + 1) (B + 1)
    apply stepStar_trans h
    ring_nf; finish

-- R5+R2 chain: a,e → d
theorem r5r2_chain : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, 2*k+e⟩ [fm]⊢* ⟨a, 0, 0, d+2*k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) + e = (2 * k + e) + 2 from by ring]
  step fm
  step fm
  apply stepStar_trans (ih a (d + 2) e)
  ring_nf; finish

-- Main transition
theorem main_trans (a D : ℕ) : ⟨a+1, 0, 0, 2*(D+1), 0⟩ [fm]⊢⁺ ⟨a+2*D+3, 0, 0, 2*(D+4), 0⟩ := by
  rw [show 2 * (D + 1) = (2 * D + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, (2 * D + 1) + 1, 0⟩ = some ⟨a, 0 + 1, 0, 2 * D + 4, 0⟩
    simp [fm]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a, 0 + 1, 0, 2 * D + 4, 0⟩ = some ⟨a, 0, 0 + 1, 2 * D + 4, 0⟩
    simp [fm]
  -- R1+R3 chain
  apply stepStar_trans
  · rw [show 2 * D + 4 = (2 * D + 3) + 1 from by ring]
    exact r1r3_chain_e0 (2 * D + 3) a 0
  -- R3 chain (b → c)
  apply stepStar_trans
  · have h := b_to_c_e0 (a := a + (2 * D + 3) + 1) (2 * D + 5) 0 0
    rw [show 0 + (2 * D + 3) + 2 = 0 + (2 * D + 5) from by ring] at *
    exact h
  -- R4 chain (c → e)
  apply stepStar_trans
  · have h := c_to_e (a := a + (2 * D + 3) + 1) (2 * D + 5) 0 0
    exact h
  -- R5+R2 chain (first pass)
  apply stepStar_trans
  · have h := r5r2_chain (D + 2) (a + D + 2) 0 1
    rw [show a + D + 2 + (D + 2) = a + (2 * D + 3) + 1 from by ring,
        show 2 * (D + 2) + 1 = 0 + (2 * D + 5) from by ring] at h
    exact h
  -- R5 + R3
  apply stepStar_trans
  · rw [show 0 + 2 * (D + 2) = (2 * D + 3) + 1 from by ring]
    apply step_stepStar
    show fm ⟨(a + D + 2), 0, 0, (2 * D + 3) + 1, 1⟩ = some ⟨a + D + 1, 0 + 1, 0, 2 * D + 6, 1⟩
    simp [fm]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨a + D + 1, 0 + 1, 0, 2 * D + 6, 1⟩ = some ⟨a + D + 1, 0, 0 + 1, 2 * D + 6, 1⟩
    simp [fm]
  -- R1+R3 chain (e=1)
  apply stepStar_trans
  · rw [show 2 * D + 6 = (2 * D + 5) + 1 from by ring]
    exact r1r3_chain_e1 (2 * D + 5) (a + D + 1) 0
  -- R3 chain (b → c, e=1)
  apply stepStar_trans
  · have h := b_to_c_e1 (a := a + D + 1 + (2 * D + 5) + 1) (2 * D + 7) 0 0
    rw [show 0 + (2 * D + 5) + 2 = 0 + (2 * D + 7) from by ring] at *
    exact h
  -- R4 chain (c → e)
  apply stepStar_trans
  · have h := c_to_e (a := a + D + 1 + (2 * D + 5) + 1) (2 * D + 7) 0 1
    exact h
  -- R5+R2 chain (second pass)
  have h := r5r2_chain (D + 4) (a + 2 * D + 3) 0 0
  rw [show a + 2 * D + 3 + (D + 4) = a + D + 1 + (2 * D + 5) + 1 from by ring,
      show 2 * (D + 4) + 0 = 1 + (2 * D + 7) from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 6, 0⟩) (by execute fm 38)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, D⟩ ↦ ⟨a+1, 0, 0, 2*(D+1), 0⟩) ⟨0, 2⟩
  intro ⟨a, D⟩; exact ⟨⟨a + 2*D + 2, D + 3⟩, by
    show ⟨a+1, 0, 0, 2*(D+1), 0⟩ [fm]⊢⁺ ⟨(a+2*D+2)+1, 0, 0, 2*((D+3)+1), 0⟩
    rw [show (a + 2 * D + 2) + 1 = a + 2 * D + 3 from by ring,
        show 2 * ((D + 3) + 1) = 2 * (D + 4) from by ring]
    exact main_trans a D⟩
