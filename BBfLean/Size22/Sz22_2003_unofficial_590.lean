import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #590: [35/6, 121/2, 28/55, 3/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  1 -1
 0  1  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_590

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: transfer d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R4 from zero: (0, 0, 0, k, e) →* (0, k, 0, 0, e)
theorem d_to_b₀ : ⟨0, 0, 0, k, e⟩ [fm]⊢* ⟨0, k, 0, 0, e⟩ := by
  have h := d_to_b (d := 0) (e := e) k 0
  simp only [Nat.zero_add] at h; exact h

-- R1R1R3 chain: each round consumes 2 from b, 1 from e, produces 1 c and 3 d
theorem r1r1r3_chain : ∀ k b c d e, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+3*k, e⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R2R2R3 chain: each round consumes 1 from c, produces 1 d and 3 e
theorem r2r2r3_chain : ∀ k c d e, ⟨2, 0, c+k, d, e⟩ [fm]⊢* ⟨2, 0, c, d+k, e+3*k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Combined phase for odd: from (2, 2m+2, 0, 1, 2m+1) to (2, 0, 0, 4m+5, 4m+3)
theorem odd_inner : ⟨2, 2*m+2, 0, 1, 2*m+1⟩ [fm]⊢* ⟨2, 0, 0, 4*m+5, 4*m+3⟩ := by
  -- r1r1r3 × (m+1): (2, 0+2*(m+1), 0, 1, m+(m+1))
  have h1 := r1r1r3_chain (m+1) 0 0 1 m
  simp only [Nat.zero_add] at h1
  -- h1: (2, 2*(m+1), 0, 1, m+(m+1)) →* (2, 0, m+1, 1+3*(m+1), m)
  rw [show 2*m+2 = 2*(m+1) from by ring, show 2*m+1 = m+(m+1) from by ring]
  apply stepStar_trans h1
  -- r2r2r3 × (m+1): (2, 0, 0+(m+1), 1+3*(m+1), m)
  have h2 := r2r2r3_chain (m+1) 0 (1+3*(m+1)) m
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  ring_nf; finish

-- Combined phase for even: from (2, 2m+1, 0, 1, 2m) to (2, 0, 0, 4m+3, 4m+1)
theorem even_inner : ⟨2, 2*m+1, 0, 1, 2*m⟩ [fm]⊢* ⟨2, 0, 0, 4*m+3, 4*m+1⟩ := by
  -- r1r1r3 × m
  have h1 := r1r1r3_chain m 1 0 1 m
  simp only [Nat.zero_add] at h1
  -- h1: (2, 1+2*m, 0, 1, m+m) →* (2, 1, m, 1+3*m, m)
  -- Rewrite h1 source to match goal
  rw [show 1 + 2 * m = 2*m+1 from by ring, show m + m = 2*m from by ring] at h1
  apply stepStar_trans h1
  -- R1, R2, R3
  step fm; step fm; step fm
  -- r2r2r3 × m
  have h2 := r2r2r3_chain m 0 (3+3*m) (m+1)
  simp only [Nat.zero_add] at h2
  -- Rewrite h2 source to match the current goal
  rw [show 3 + 3 * m = 1 + 3 * m + 1 + 1 from by ring] at h2
  apply stepStar_trans h2
  ring_nf; finish

-- Odd transition: (0,0,0,2m+1,2m+3) →⁺ (0,0,0,4m+5,4m+7)
theorem odd_trans : ⟨0, 0, 0, 2*m+1, 2*m+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*m+5, 4*m+7⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_b₀ (k := 2*m+1))
  rw [show (2*m+3 : ℕ) = (2*m+2)+1 from by ring]
  step fm
  rw [show (2*m+2 : ℕ) = (2*m+1)+1 from by ring]
  step fm
  apply stepStar_trans odd_inner
  step fm; step fm; ring_nf; finish

-- Even transition: (0,0,0,2m,2m+2) →⁺ (0,0,0,4m+3,4m+5)
theorem even_trans : ⟨0, 0, 0, 2*m, 2*m+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*m+3, 4*m+5⟩ := by
  apply stepStar_stepPlus_stepPlus (d_to_b₀ (k := 2*m))
  rw [show (2*m+2 : ℕ) = (2*m+1)+1 from by ring]
  step fm
  rw [show (2*m+1 : ℕ) = (2*m)+1 from by ring]
  step fm
  apply stepStar_trans even_inner
  step fm; step fm; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d, d+2⟩) 0
  intro d
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact ⟨4*m+3, even_trans⟩
  · subst hm
    exact ⟨4*m+5, odd_trans⟩
