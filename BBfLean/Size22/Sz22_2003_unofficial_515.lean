import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #515: [28/15, 3/22, 65/2, 11/7, 63/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  2  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_515

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | _ => none

-- R3 repeated: drain a, fill c and f
theorem a_to_cf : ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  have h : ∀ k c f, ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
    intro k; induction' k with k ih <;> intro c f
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h k c f

-- R4 repeated: drain d, fill e
theorem d_to_e : ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
  have h : ∀ k d e, ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
    intro k; induction' k with k ih <;> intro d e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h k d e

-- R5, R1, R1: opening
theorem opening : ⟨0, 0, c+2, 0, e, f+1⟩ [fm]⊢⁺ ⟨4, 0, c, 3, e, f⟩ := by
  step fm; step fm; step fm; finish

-- (R2, R1) chain: net +1 to a and d, -1 to c and e per round
theorem r2r1_chain : ⟨a+1, 0, c+k, d, e+k, f⟩ [fm]⊢* ⟨a+1+k, 0, c, d+k, e, f⟩ := by
  have h : ∀ k a c d e, ⟨a+1, 0, c+k, d, e+k, f⟩ [fm]⊢* ⟨a+1+k, 0, c, d+k, e, f⟩ := by
    intro k; induction' k with k ih <;> intro a c d e
    · exists 0
    rw [show c + (k+1) = (c+k) + 1 from by ring]
    rw [show e + (k+1) = (e+k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a+1) c (d+1) e)
    ring_nf; finish
  exact h k a c d e

-- R2 repeated: drain e, fill b
theorem e_to_b : ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
  have h : ∀ k a b, ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
    intro k; induction' k with k ih <;> intro a b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish
  exact h k a b

-- (R3, R1) chain: net +1 to a, d, f, -1 to b per round
theorem r3r1_chain : ⟨a+1, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+1+k, b, 0, d+k, 0, f+k⟩ := by
  have h : ∀ k a b d f, ⟨a+1, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+1+k, b, 0, d+k, 0, f+k⟩ := by
    intro k; induction' k with k ih <;> intro a b d f
    · exists 0
    rw [show b + (k+1) = (b+k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a+1) b (d+1) (f+1))
    ring_nf; finish
  exact h k a b d f

-- Main transition
theorem main_trans (n f : ℕ) :
    ⟨2*n+3, 0, 0, 3*n+3, 0, f⟩ [fm]⊢⁺ ⟨2*n+5, 0, 0, 3*n+6, 0, f+3*n+4⟩ := by
  -- Phase 1: R3 × (2n+3): drain a, fill c and f
  have h1 := a_to_cf (a := 0) (k := 2*n+3) (c := 0) (d := 3*n+3) (f := f)
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R4 × (3n+3): drain d, fill e
  have h2 := d_to_e (c := 2*n+3) (k := 3*n+3) (d := 0) (e := 0) (f := f+(2*n+3))
  simp only [Nat.zero_add] at h2
  apply stepStar_stepPlus_stepPlus h2
  -- Phase 3a: R5, R1, R1
  rw [show (2*n+3 : ℕ) = (2*n+1) + 2 from by ring]
  rw [show f + (2*n+3) = (f+(2*n+2)) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (c := 2*n+1) (e := 3*n+3) (f := f+(2*n+2)))
  -- Phase 3b: (R2, R1) × (2n+1)
  -- State: (4, 0, 2n+1, 3, 3n+3, f+(2n+2))
  -- r2r1_chain with a=3, k=2n+1, c=0, d=3, e=n+2:
  -- Start: (3+1, 0, 0+(2n+1), 3, (n+2)+(2n+1), f+(2n+2)) = (4, 0, 2n+1, 3, 3n+3, f+(2n+2))
  -- End: (3+1+(2n+1), 0, 0, 3+(2n+1), n+2, f+(2n+2)) = (2n+5, 0, 0, 2n+4, n+2, f+(2n+2))
  have h3 := r2r1_chain (a := 3) (k := 2*n+1) (c := 0) (d := 3) (e := n+2) (f := f+(2*n+2))
  rw [show 0 + (2*n+1) = 2*n+1 from by ring] at h3
  rw [show (n+2) + (2*n+1) = 3*n+3 from by ring] at h3
  rw [show 3 + 1 + (2*n+1) = 2*n+5 from by ring] at h3
  rw [show 3 + (2*n+1) = 2*n+4 from by ring] at h3
  apply stepStar_trans h3
  -- Phase 3d: R2 × (n+2): drain e, fill b
  -- State: (2n+5, 0, 0, 2n+4, n+2, f+(2n+2))
  have h4 := e_to_b (a := n+3) (k := n+2) (b := 0) (d := 2*n+4) (f := f+(2*n+2))
  rw [show (n+3) + (n+2) = 2*n+5 from by ring] at h4
  rw [show 0 + (n+2) = n+2 from by ring] at h4
  apply stepStar_trans h4
  -- Phase 4: (R3, R1) × (n+2)
  -- State: (n+3, n+2, 0, 2n+4, 0, f+(2n+2))
  have h5 := r3r1_chain (a := n+2) (k := n+2) (b := 0) (d := 2*n+4) (f := f+(2*n+2))
  rw [show 0 + (n+2) = n+2 from by ring] at h5
  rw [show (n+2) + 1 + (n+2) = 2*n+5 from by ring] at h5
  rw [show (2*n+4) + (n+2) = 3*n+6 from by ring] at h5
  rw [show f + (2*n+2) + (n+2) = f + 3*n + 4 from by ring] at h5
  exact stepStar_trans h5 (by finish)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 3, 0, 1⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = ⟨2*n+3, 0, 0, 3*n+3, 0, f⟩)
  · intro c ⟨n, f, hq⟩; subst hq
    exact ⟨⟨2*n+5, 0, 0, 3*n+6, 0, f+3*n+4⟩,
      ⟨n+1, f+3*n+4, by ring_nf⟩, main_trans n f⟩
  · exact ⟨0, 1, by ring_nf⟩
