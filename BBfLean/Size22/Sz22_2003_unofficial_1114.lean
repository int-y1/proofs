import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1114: [5/6, 4/35, 5929/2, 3/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  2  2
 0  1  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1114

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R3 chain: drain a via R3.
-- ⟨a+k, 0, 0, d, e⟩ →* ⟨a, 0, 0, d+2*k, e+2*k⟩
theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) (e + 2))
    ring_nf; finish

-- R4 chain: drain e to b.
-- ⟨0, b, 0, d, e+k⟩ →* ⟨0, b+k, 0, d, e⟩
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

-- R1R2 interleave chain: each round does R1, R1, R2 (3 steps).
-- ⟨2, b+2*k, c, d+k, 1⟩ →* ⟨2, b, c+k, d, 1⟩
theorem r1r2_chain : ∀ k, ∀ b c d, ⟨2, b + 2 * k, c, d + k, (1 : ℕ)⟩ [fm]⊢* ⟨2, b, c + k, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1))
    step fm; step fm; step fm; ring_nf; finish

-- R2 chain with b=0.
-- ⟨a, 0, c+k, d+k, e⟩ →* ⟨a+2*k, 0, c, d, e⟩
theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

-- R3R2R2 chain: K cycles.
-- ⟨a+1, 0, 2*K+1, 0, e⟩ →* ⟨a+3*K+1, 0, 1, 0, e+2*K⟩
theorem r3r2r2_chain : ∀ K, ∀ a e, ⟨a + 1, 0, 2 * K + 1, 0, e⟩ [fm]⊢* ⟨a + 3 * K + 1, 0, 1, 0, e + 2 * K⟩ := by
  intro K; induction' K with K ih <;> intro a e
  · exists 0
  · rw [show 2 * (K + 1) + 1 = (2 * K + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) (e + 2))
    ring_nf; finish

-- Main transition using parameterization a = m + n + 2.
-- ⟨m+n+2, 0, 0, 1, 2*n+3⟩ ⊢⁺ ⟨2*m+3*n+6, 0, 0, 1, 2*n+5⟩
theorem main_transition (m n : ℕ) :
    ⟨m + n + 2, 0, 0, 1, 2 * n + 3⟩ [fm]⊢⁺ ⟨2 * m + 3 * n + 6, 0, 0, 1, 2 * n + 5⟩ := by
  -- Phase 1: R3 chain (m+n+2 steps): ⟨m+n+2, 0, 0, 1, 2*n+3⟩ →* ⟨0, 0, 0, 2m+2n+5, 2m+4n+7⟩
  -- Phase 2: R4 chain: →* ⟨0, 2m+4n+7, 0, 2m+2n+5, 0⟩
  -- Phase 3: R5+R1+R2 (3 steps): → ⟨2, 2m+4n+6, 0, 2m+2n+3, 1⟩
  -- Phase 4: R1R2 chain (m+2n+3 rounds): →* ⟨2, 0, m+2n+3, m, 1⟩
  -- Phase 5: R2 chain (m steps): →* ⟨2m+2, 0, 2n+3, 0, 1⟩
  -- Phase 6: R3R2R2 chain (n+1 cycles) + R3+R2: →* ⟨2m+3n+6, 0, 0, 1, 2n+5⟩

  -- Start: apply R3 chain, then the rest is ⊢⁺
  have h1 : ⟨m + n + 2, 0, 0, 1, 2 * n + 3⟩ [fm]⊢* ⟨0, 0, 0, 2 * m + 2 * n + 5, 2 * m + 4 * n + 7⟩ := by
    rw [show m + n + 2 = 0 + (m + n + 2) from by ring]
    apply stepStar_trans (r3_chain (m + n + 2) 0 1 (2 * n + 3))
    ring_nf; finish
  have h2 : ⟨0, 0, 0, 2 * m + 2 * n + 5, 2 * m + 4 * n + 7⟩ [fm]⊢* ⟨0, 2 * m + 4 * n + 7, 0, 2 * m + 2 * n + 5, 0⟩ := by
    rw [show 2 * m + 4 * n + 7 = 0 + (2 * m + 4 * n + 7) from by ring]
    apply stepStar_trans (r4_chain (2 * m + 4 * n + 7) 0 (2 * m + 2 * n + 5) 0)
    ring_nf; finish
  have h3 : ⟨0, 2 * m + 4 * n + 7, 0, 2 * m + 2 * n + 5, 0⟩ [fm]⊢* ⟨2, 2 * m + 4 * n + 6, 0, 2 * m + 2 * n + 3, (1 : ℕ)⟩ := by
    step fm; step fm; step fm; finish
  have h4 : ⟨2, 2 * m + 4 * n + 6, 0, 2 * m + 2 * n + 3, (1 : ℕ)⟩ [fm]⊢* ⟨2, 0, m + 2 * n + 3, m, 1⟩ := by
    have := r1r2_chain (m + 2 * n + 3) 0 0 m
    rw [show 0 + 2 * (m + 2 * n + 3) = 2 * m + 4 * n + 6 from by ring,
        show m + (m + 2 * n + 3) = 2 * m + 2 * n + 3 from by ring,
        show 0 + (m + 2 * n + 3) = m + 2 * n + 3 from by ring] at this
    exact this
  have h5 : ⟨2, 0, m + 2 * n + 3, m, (1 : ℕ)⟩ [fm]⊢* ⟨2 * m + 2, 0, 2 * n + 3, 0, 1⟩ := by
    have := r2_chain m 2 (2 * n + 3) 0 1
    rw [show (2 * n + 3) + m = m + 2 * n + 3 from by ring,
        show (0 : ℕ) + m = m from by ring] at this
    apply stepStar_trans this
    ring_nf; finish
  have h6 : ⟨2 * m + 2, 0, 2 * n + 3, 0, (1 : ℕ)⟩ [fm]⊢* ⟨2 * m + 3 * n + 5, 0, 1, 0, 2 * n + 3⟩ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring,
        show 2 * n + 3 = 2 * (n + 1) + 1 from by ring]
    apply stepStar_trans (r3r2r2_chain (n + 1) (2 * m + 1) 1)
    ring_nf; finish
  have h7 : ⟨2 * m + 3 * n + 5, 0, 1, 0, 2 * n + 3⟩ [fm]⊢⁺ ⟨2 * m + 3 * n + 6, 0, 0, 1, 2 * n + 5⟩ := by
    step fm; step fm; ring_nf; finish
  exact stepStar_stepPlus_stepPlus (stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))) h7

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 3⟩)
  · execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, n⟩ ↦ ⟨m + n + 2, 0, 0, 1, 2 * n + 3⟩) ⟨0, 0⟩
  intro ⟨m, n⟩; exists ⟨2 * m + 2 * n + 3, n + 1⟩
  show ⟨m + n + 2, 0, 0, 1, 2 * n + 3⟩ [fm]⊢⁺ ⟨(2 * m + 2 * n + 3) + (n + 1) + 2, 0, 0, 1, 2 * (n + 1) + 3⟩
  rw [show (2 * m + 2 * n + 3) + (n + 1) + 2 = 2 * m + 3 * n + 6 from by ring,
      show 2 * (n + 1) + 3 = 2 * n + 5 from by ring]
  exact main_transition m n

end Sz22_2003_unofficial_1114
