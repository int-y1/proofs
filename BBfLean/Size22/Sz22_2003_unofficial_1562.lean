import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1562: [7/45, 20/77, 121/5, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  0
 2  0  1 -1 -1
 0  0 -1  0  2
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1562

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

-- R5+R1 chain: k rounds, each pair does R5 then R1.
theorem r5r1_chain : ∀ k, ∀ a b d,
    ⟨a + k, b + 2 * k, 0, d, 0⟩ [fm]⊢* ⟨a, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a b (d + 2)); ring_nf; finish

-- R3R2R2 chain with b=0.
theorem r3r2r2_b0 : ∀ j, ∀ A C D,
    ⟨A, 0, C + 1, D + 2 * j, 0⟩ [fm]⊢* ⟨A + 4 * j, 0, C + 1 + j, D, 0⟩ := by
  intro j; induction' j with j ih <;> intro A C D
  · exists 0
  · rw [show D + 2 * (j + 1) = (D + 2 * j) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 4) (C + 1) D)
    rw [show C + 1 + (j + 1) = (C + 1 + j) + 1 from by ring]; ring_nf; finish

-- R3R2R2 chain with b=1.
theorem r3r2r2_b1 : ∀ j, ∀ A C D,
    ⟨A, 1, C + 1, D + 2 * j, 0⟩ [fm]⊢* ⟨A + 4 * j, 1, C + 1 + j, D, 0⟩ := by
  intro j; induction' j with j ih <;> intro A C D
  · exists 0
  · rw [show D + 2 * (j + 1) = (D + 2 * j) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (A + 4) (C + 1) D)
    rw [show C + 1 + (j + 1) = (C + 1 + j) + 1 from by ring]; ring_nf; finish

-- R3 drain c with b=0, d=0.
theorem r3_drain_b0 : ∀ k, ∀ A E,
    ⟨A, 0, k, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · step fm
    apply stepStar_trans (ih A (E + 2)); ring_nf; finish

-- R3 drain c with b=1, d=0.
theorem r3_drain_b1 : ∀ k, ∀ A E,
    ⟨A, 1, k, 0, E⟩ [fm]⊢* ⟨A, 1, 0, 0, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  · step fm
    apply stepStar_trans (ih A (E + 2)); ring_nf; finish

-- R4 drain e to b.
theorem r4_drain : ∀ k, ∀ A B,
    ⟨A, B, 0, 0, k⟩ [fm]⊢* ⟨A, B + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B
  · exists 0
  · step fm
    apply stepStar_trans (ih A (B + 1)); ring_nf; finish

-- Odd b transition: (A+K+1, 2K+1, 0, 0, 0) ⊢⁺ (A+4K+2, 2K+4, 0, 0, 0).
theorem odd_trans (A K : ℕ) :
    ⟨A + K + 1, 2 * K + 1, 0, 0, 0⟩ [fm]⊢⁺ ⟨A + 4 * K + 2, 2 * K + 4, 0, 0, 0⟩ := by
  -- R5R1 chain (K rounds)
  rw [show A + K + 1 = (A + 1) + K from by ring,
      show 2 * K + 1 = 1 + 2 * K from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain K (A + 1) 1 0)
  rw [show (0 + 2 * K : ℕ) = 2 * K from by ring]
  -- R5 (symbolic)
  apply step_stepStar_stepPlus
    (show ⟨A + 1, 1, 0, 2 * K, 0⟩ [fm]⊢ ⟨A, 1, 1, 2 * K + 1, 0⟩ from by simp [fm])
  -- R3R2R2 chain (K rounds, b=1)
  rw [show (2 * K + 1 : ℕ) = 1 + 2 * K from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_b1 K A 0 1)
  rw [show 0 + 1 + K = K + 1 from by ring]
  -- R3, R2
  step fm; step fm
  -- R3 drain (K+1 rounds)
  apply stepStar_trans (r3_drain_b1 (K + 1) (A + 4 * K + 2) 1)
  rw [show 1 + 2 * (K + 1) = 2 * K + 3 from by ring]
  -- R4 drain (2K+3 rounds)
  apply stepStar_trans (r4_drain (2 * K + 3) (A + 4 * K + 2) 1)
  rw [show 1 + (2 * K + 3) = 2 * K + 4 from by ring]; finish

-- Even b transition: (A+K+1, 2K, 0, 0, 0) ⊢⁺ (A+4K+2, 2K+3, 0, 0, 0).
theorem even_trans (A K : ℕ) :
    ⟨A + K + 1, 2 * K, 0, 0, 0⟩ [fm]⊢⁺ ⟨A + 4 * K + 2, 2 * K + 3, 0, 0, 0⟩ := by
  -- R5R1 chain (K rounds)
  rw [show A + K + 1 = (A + 1) + K from by ring,
      show 2 * K = 0 + 2 * K from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain K (A + 1) 0 0)
  rw [show (0 + 2 * K : ℕ) = 2 * K from by ring]
  -- R5 (symbolic)
  apply step_stepStar_stepPlus
    (show ⟨A + 1, 0, 0, 2 * K, 0⟩ [fm]⊢ ⟨A, 0, 1, 2 * K + 1, 0⟩ from by simp [fm])
  -- R3R2R2 chain (K rounds, b=0)
  rw [show (2 * K + 1 : ℕ) = 1 + 2 * K from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_b0 K A 0 1)
  rw [show 0 + 1 + K = K + 1 from by ring]
  -- R3, R2
  step fm; step fm
  -- R3 drain (K+1 rounds)
  apply stepStar_trans (r3_drain_b0 (K + 1) (A + 4 * K + 2) 1)
  rw [show 1 + 2 * (K + 1) = 2 * K + 3 from by ring]
  -- R4 drain (2K+3 rounds)
  apply stepStar_trans (r4_drain (2 * K + 3) (A + 4 * K + 2) 0)
  rw [show 0 + (2 * K + 3) = 2 * K + 3 from by ring]; finish

-- 2-step macro: (F+k+2, 2k+3, 0, 0, 0) ⊢⁺ (F+7k+16, 2k+9, 0, 0, 0).
theorem main_trans (F k : ℕ) :
    ⟨F + k + 2, 2 * k + 3, 0, 0, 0⟩ [fm]⊢⁺ ⟨F + 7 * k + 16, 2 * k + 9, 0, 0, 0⟩ := by
  -- Odd step with K = k+1
  rw [show F + k + 2 = F + (k + 1) + 1 from by ring,
      show 2 * k + 3 = 2 * (k + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (odd_trans F (k + 1))
  rw [show F + 4 * (k + 1) + 2 = (F + 3 * k + 2) + (k + 3) + 1 from by ring,
      show 2 * (k + 1) + 4 = 2 * (k + 3) from by ring]
  -- Even step with K = k+3
  have h := even_trans (F + 3 * k + 2) (k + 3)
  rw [show (F + 3 * k + 2) + 4 * (k + 3) + 2 = F + 7 * k + 16 from by ring,
      show 2 * (k + 3) + 3 = 2 * k + 9 from by ring] at h
  exact stepPlus_stepStar h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 3, 0, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + p.2 + 2, 2 * p.2 + 3, 0, 0, 0⟩) ⟨0, 0⟩
  intro ⟨F, k⟩
  exact ⟨⟨F + 6 * k + 11, k + 3⟩, by
    show ⟨F + k + 2, 2 * k + 3, 0, 0, 0⟩ [fm]⊢⁺
      ⟨F + 6 * k + 11 + (k + 3) + 2, 2 * (k + 3) + 3, 0, 0, 0⟩
    rw [show F + 6 * k + 11 + (k + 3) + 2 = F + 7 * k + 16 from by ring,
        show 2 * (k + 3) + 3 = 2 * k + 9 from by ring]
    exact main_trans F k⟩

end Sz22_2003_unofficial_1562
