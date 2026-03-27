import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #641: [35/6, 143/2, 4/55, 3/7, 70/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_641

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c+1, d+1, e, f⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction k with
  | zero => intro b; exists 0
  | succ k ih =>
    intro b
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish

-- R3,R2,R2 drain: (0,0,c+k,d,e+k,f) ⊢* (0,0,c,d,e+2k,f+2k)
theorem r3r2r2_drain : ∀ k c e f, ⟨0, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 * k, f + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro c e f; exists 0
  | succ k ih =>
    intro c e f
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + k + 1 + 1 = (e + 2) + k from by ring,
        show f + 1 + 1 = f + 2 from by ring]
    apply stepStar_trans (ih c (e + 2) (f + 2))
    ring_nf; finish

-- R1,R1,R3 interleave: (2,b+2k,c,d,e+k,f) ⊢* (2,b,c+k,d+2k,e,f)
theorem r1r1r3_chain : ∀ k c d e, ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

-- Base case: n=0
theorem base0 : ⟨0, 0, 0, 0, 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 3, f + 3⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Transition for odd n: (0,0,0,2m+1,4m+3,f+1) →⁺ (0,0,0,2m+2,4m+5,f+2m+4)
theorem trans_odd (m f : ℕ) : ⟨0, 0, 0, 2*m+1, 4*m+3, f+1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*m+2, 4*m+5, f+2*m+4⟩ := by
  -- Phase 1: R4*(2m+1)
  have h1 : ⟨0, 0, 0, 2*m+1, 4*m+3, f+1⟩ [fm]⊢* ⟨0, 2*m+1, 0, 0, 4*m+3, f+1⟩ := by
    rw [show (2*m+1 : ℕ) = 0 + (2*m+1) from by ring]; exact d_to_b _ _
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R5, R1, R3
  step fm; step fm; step fm
  -- Now at (2, 2*m, 1, 2, 4*m+2, f)
  -- Phase 3: R1,R1,R3 chain (m rounds)
  have h3 : ⟨2, 2*m, 1, 2, 4*m+2, f⟩ [fm]⊢* ⟨2, 0, m+1, 2*m+2, 3*m+2, f⟩ := by
    rw [show (2*m : ℕ) = 0 + 2*m from by ring,
        show (4*m+2 : ℕ) = (3*m+2) + m from by ring]
    have := r1r1r3_chain (b := 0) (f := f) m 1 2 (3*m+2)
    rw [show (0 : ℕ) + 2*m = 2*m from by ring,
        show (3*m+2 : ℕ) + m = 4*m+2 from by ring] at this
    convert this using 2; ring_nf
  apply stepStar_trans h3
  -- Phase 4: R2, R2
  step fm; step fm
  -- Phase 5: drain (m+1 rounds)
  have h5 : ⟨0, 0, m+1, 2*m+2, 3*m+4, f+2⟩ [fm]⊢* ⟨0, 0, 0, 2*m+2, 4*m+5, f+2*m+4⟩ := by
    rw [show (m+1 : ℕ) = 0 + (m+1) from by ring,
        show (3*m+4 : ℕ) = (2*m+3) + (m+1) from by ring]
    have := r3r2r2_drain (d := 2*m+2) (m+1) 0 (2*m+3) (f+2)
    rw [show (2*m+3 : ℕ) + (m+1) = 3*m+4 from by ring] at this
    convert this using 2; ring_nf
  apply stepStar_trans h5
  finish

-- Transition for even n≥2: (0,0,0,2m+2,4m+5,f+1) →⁺ (0,0,0,2m+3,4m+7,f+2m+5)
theorem trans_even (m f : ℕ) : ⟨0, 0, 0, 2*m+2, 4*m+5, f+1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*m+3, 4*m+7, f+2*m+5⟩ := by
  -- Phase 1: R4*(2m+2)
  have h1 : ⟨0, 0, 0, 2*m+2, 4*m+5, f+1⟩ [fm]⊢* ⟨0, 2*m+2, 0, 0, 4*m+5, f+1⟩ := by
    rw [show (2*m+2 : ℕ) = 0 + (2*m+2) from by ring]; exact d_to_b _ _
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: R5, R1, R3
  step fm; step fm; step fm
  -- Now at (2, 2*m+1, 1, 2, 4*m+4, f)
  -- Phase 3: R1,R1,R3 chain (m rounds)
  have h3 : ⟨2, 2*m+1, 1, 2, 4*m+4, f⟩ [fm]⊢* ⟨2, 1, m+1, 2*m+2, 3*m+4, f⟩ := by
    rw [show (2*m+1 : ℕ) = 1 + 2*m from by ring,
        show (4*m+4 : ℕ) = (3*m+4) + m from by ring]
    have := r1r1r3_chain (b := 1) (f := f) m 1 2 (3*m+4)
    rw [show (1 : ℕ) + 2*m = 2*m+1 from by ring,
        show (3*m+4 : ℕ) + m = 4*m+4 from by ring] at this
    convert this using 2; ring_nf
  apply stepStar_trans h3
  -- Phase 4: R1, R2
  step fm; step fm
  -- Phase 5: drain (m+2 rounds)
  have h5 : ⟨0, 0, m+2, 2*m+3, 3*m+5, f+1⟩ [fm]⊢* ⟨0, 0, 0, 2*m+3, 4*m+7, f+2*m+5⟩ := by
    rw [show (m+2 : ℕ) = 0 + (m+2) from by ring,
        show (3*m+5 : ℕ) = (2*m+3) + (m+2) from by ring]
    have := r3r2r2_drain (d := 2*m+3) (m+2) 0 (2*m+3) (f+1)
    rw [show (2*m+3 : ℕ) + (m+2) = 3*m+5 from by ring] at this
    convert this using 2; ring_nf
  apply stepStar_trans h5
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = ⟨0, 0, 0, n, 2*n+1, f+1⟩)
  · intro c ⟨n, f, hq⟩; subst hq
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2*m from by ring] at hm; subst hm
      rcases m with _ | m
      · -- n = 0
        exact ⟨⟨0, 0, 0, 1, 3, f+3⟩, ⟨1, f+2, by ring_nf⟩, base0⟩
      · -- n = 2*(m+1) even
        refine ⟨⟨0, 0, 0, 2*m+3, 4*m+7, f+2*m+5⟩, ⟨2*m+3, f+2*m+4, ?_⟩, ?_⟩
        · congr 1; ring_nf
        · rw [show 2*(2*(m+1))+1 = 4*m+5 from by ring,
              show 2*(m+1) = 2*m+2 from by ring]
          exact trans_even m f
    · -- n = 2*m+1 odd
      subst hm
      refine ⟨⟨0, 0, 0, 2*m+2, 4*m+5, f+2*m+4⟩, ⟨2*m+2, f+2*m+3, ?_⟩, ?_⟩
      · congr 1; ring_nf
      · rw [show 2*(2*m+1)+1 = 4*m+3 from by ring]
        exact trans_odd m f
  · exact ⟨0, 0, by ring_nf⟩
