import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #541: [28/15, 9/22, 65/2, 11/7, 21/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  2  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_541

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R3 chain: convert a to c and f
theorem a_to_c : ∀ k c F, ⟨a+k, 0, c, d, 0, F⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, F+k⟩ := by
  intro k; induction' k with k h <;> intro c F
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R4 chain: convert d to e
theorem d_to_e : ∀ k c d F, ⟨0, 0, c, d+k, 0, F⟩ [fm]⊢* ⟨0, 0, c, d, k, F⟩ := by
  intro k; induction' k with k h <;> intro c d F
  · exists 0
  rw [show d + (k + 1) = (d + 1) + k from by ring]
  apply stepStar_trans (h c (d + 1) F); step fm; finish

-- Opening: R5, R1, R2
theorem opening_plus : ⟨0, 0, c+2, 0, e+1, F+1⟩ [fm]⊢⁺ ⟨1, 2, c+1, 2, e, F⟩ := by
  step fm; step fm; step fm; finish

-- R1, R1, R2 chain (c is the remainder)
theorem r1r1r2_chain (c : ℕ) : ∀ k A D E F,
    ⟨A, 2, 2*k+c, D, E+k, F⟩ [fm]⊢* ⟨A+3*k, 2, c, D+2*k, E, F⟩ := by
  intro k; induction' k with k h <;> intro A D E F
  · simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]; exists 0
  rw [show 2 * (k + 1) + c = (2 * k + c) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _ _); ring_nf; finish

-- Extra R1 for odd c remainder
theorem r1_odd : ⟨A, 2, 1, D, E, F⟩ [fm]⊢* ⟨A+2, 1, 0, D+1, E, F⟩ := by
  step fm; finish

-- R2 drain
theorem r2_drain (D : ℕ) : ∀ k X Y F,
    ⟨X+k, Y, 0, D, k, F⟩ [fm]⊢* ⟨X, Y+2*k, 0, D, 0, F⟩ := by
  intro k; induction' k with k h <;> intro X Y F
  · simp only [Nat.add_zero, Nat.mul_zero]; exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R3, R1 chain (needs a >= 1 for R3, expressed as a+1)
theorem r3r1_chain : ∀ k a d F,
    ⟨a+1, k, 0, d, 0, F⟩ [fm]⊢* ⟨a+1+k, 0, 0, d+k, 0, F+k⟩ := by
  intro k; induction' k with k h <;> intro a d F
  · exists 0
  step fm; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- Combined a_to_c + d_to_e
theorem phases12 (a n F : ℕ) :
    ⟨a, 0, 0, a+n, 0, F⟩ [fm]⊢* ⟨0, 0, a, 0, a+n, F+a⟩ := by
  have h1 : ⟨0+a, 0, 0, a+n, 0, F⟩ [fm]⊢* ⟨0, 0, 0+a, a+n, 0, F+a⟩ := a_to_c a 0 F
  simp only [Nat.zero_add] at h1
  have h2 : ⟨0, 0, a, 0+(a+n), 0, F+a⟩ [fm]⊢* ⟨0, 0, a, 0, a+n, F+a⟩ := d_to_e (a+n) a 0 (F+a)
  simp only [Nat.zero_add] at h2
  exact stepStar_trans h1 h2

-- Main transition
theorem main_trans (m n : ℕ) :
    ⟨m+n+2, 0, 0, m+2*n+2, 0, 2*m⟩ [fm]⊢⁺ ⟨2*m+3*n+5, 0, 0, 2*m+4*n+6, 0, 4*m+4*n+4⟩ := by
  -- Phase 1+2: a_to_c + d_to_e (⊢*)
  rw [show m+2*n+2 = (m+n+2)+n from by ring]
  -- opening gives ⊢⁺, so use phases12 as ⊢* prefix
  apply stepStar_stepPlus_stepPlus (phases12 (m+n+2) n (2*m))
  -- opening (⊢⁺): gives the strict progress
  rw [show 2*m+(m+n+2) = (3*m+n+1)+1 from by ring,
      show m+n+2 = (m+n)+2 from by ring,
      show (m+n+2)+n = (m+2*n+1)+1 from by ring]
  apply stepPlus_stepStar_stepPlus opening_plus
  -- After opening: (1, 2, m+n+1, 2, m+2*n+1, 3*m+n+1), goal is ⊢*
  -- Split on parity of m+n
  rcases Nat.even_or_odd (m + n) with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- m+n even = K+K
    rw [show m+n+1 = 2*K+1 from by omega]
    -- r1r1r2_chain: K rounds with remainder 1
    have h4 := r1r1r2_chain 1 K 1 2 (m+2*n+1-K) (3*m+n+1)
    rw [show (m+2*n+1-K)+K = m+2*n+1 from by omega] at h4
    apply stepStar_trans h4
    -- r1_odd
    apply stepStar_trans r1_odd
    -- After r1_odd: (1+3*K+2, 1, 0, 2+2*K+1, m+2*n+1-K, 3*m+n+1)
    rw [show 2+2*K+1 = m+n+3 from by omega]
    -- r2_drain
    have h5 := r2_drain (m+n+3) (m+2*n+1-K) (m+2) 1 (3*m+n+1)
    rw [show (m+2)+(m+2*n+1-K) = 1+3*K+2 from by omega,
        show 1+2*(m+2*n+1-K) = m+3*n+3 from by omega] at h5
    apply stepStar_trans h5
    -- r3r1_chain
    have h6 := r3r1_chain (m+3*n+3) (m+1) (m+n+3) (3*m+n+1)
    rw [show m+1+1 = m+2 from by ring] at h6
    apply stepStar_trans h6
    ring_nf; finish
  · -- m+n odd = 2*K+1
    rw [show m+n+1 = 2*(K+1) from by omega]
    -- r1r1r2_chain: K+1 rounds with remainder 0
    have h4 := r1r1r2_chain 0 (K+1) 1 2 (m+2*n+1-(K+1)) (3*m+n+1)
    rw [show (m+2*n+1-(K+1))+(K+1) = m+2*n+1 from by omega] at h4
    simp only [Nat.add_zero] at h4
    apply stepStar_trans h4
    -- After chain: (1+3*(K+1), 2, 0, 2+2*(K+1), m+2*n+1-(K+1), 3*m+n+1)
    rw [show 2+2*(K+1) = m+n+3 from by omega]
    -- r2_drain (no r1_odd since remainder = 0)
    have h5 := r2_drain (m+n+3) (m+2*n+1-(K+1)) (m+2) 2 (3*m+n+1)
    rw [show (m+2)+(m+2*n+1-(K+1)) = 1+3*(K+1) from by omega,
        show 2+2*(m+2*n+1-(K+1)) = m+3*n+3 from by omega] at h5
    apply stepStar_trans h5
    -- r3r1_chain
    have h6 := r3r1_chain (m+3*n+3) (m+1) (m+n+3) (3*m+n+1)
    rw [show m+1+1 = m+2 from by ring] at h6
    apply stepStar_trans h6
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0, 0⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, n⟩ ↦ ⟨m+n+2, 0, 0, m+2*n+2, 0, 2*m⟩) ⟨0, 0⟩
  intro ⟨m, n⟩; exists ⟨2*m+2*n+2, n+1⟩
  show ⟨m+n+2, 0, 0, m+2*n+2, 0, 2*m⟩ [fm]⊢⁺
    ⟨(2*m+2*n+2)+(n+1)+2, 0, 0, (2*m+2*n+2)+2*(n+1)+2, 0, 2*(2*m+2*n+2)⟩
  have h := main_trans m n
  rw [show (2*m+2*n+2)+(n+1)+2 = 2*m+3*n+5 from by ring,
      show (2*m+2*n+2)+2*(n+1)+2 = 2*m+4*n+6 from by ring,
      show 2*(2*m+2*n+2) = 4*m+4*n+4 from by ring]
  exact h

end Sz22_2003_unofficial_541
