import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #517: [28/15, 3/22, 65/2, 11/7, 99/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_517

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | _ => none

-- R3 chain: a to c and f
theorem r3_chain : ∀ k a c d f, ⟨a + k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c + k, d, 0, f + k⟩ := by
  intro k; induction' k with k h <;> intro a c d f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R4 chain: d to e
theorem d_to_e : ∀ k c d e f, ⟨0, 0, c, d + k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k h <;> intro c d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R2,R1 chain: each pair consumes 1 from c and e, adds 1 to a and d
theorem r2r1_chain : ∀ k a c d e f, ⟨a + 1, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 1 + k, 0, c, d + k, e, f⟩ := by
  intro k; induction' k with k h <;> intro a c d e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega,
      show e + (k + 1) = (e + k) + 1 from by omega]
  step fm; step fm
  apply stepStar_trans (h _ _ _ _ _)
  ring_nf; finish

-- R2 chain: a,e to b (when c=0)
theorem r2_chain : ∀ k a b d e f, ⟨a + k, b, 0, d, e + k, f⟩ [fm]⊢* ⟨a, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro a b d e f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by omega,
      show e + (k + 1) = (e + k) + 1 from by omega]
  step fm
  apply stepStar_trans (h _ _ _ _ _)
  ring_nf; finish

-- R3,R1 chain: each pair (R3 then R1) with a>=1, b>=1
-- (a+1, b+k, 0, d, 0, f) ->* (a+k+1, b, 0, d+k, 0, f+k)
theorem r3r1_chain : ∀ k a b d f, ⟨a + 1, b + k, 0, d, 0, f⟩ [fm]⊢* ⟨a + k + 1, b, 0, d + k, 0, f + k⟩ := by
  intro k; induction' k with k h <;> intro a b d f
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by omega]
  step fm; step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- Main transition: (2n+3, 0, 0, 3n+3, 0, g+2) →⁺ (2n+5, 0, 0, 3n+6, 0, g+3n+7)
theorem main_trans (n g : ℕ) :
    ⟨2*n+3, 0, 0, 3*n+3, 0, g+2⟩ [fm]⊢⁺ ⟨2*n+5, 0, 0, 3*n+6, 0, g+3*n+7⟩ := by
  -- Phase 1: R3 × (2n+3): (2n+3, 0, 0, 3n+3, 0, g+2) →* (0, 0, 2n+3, 3n+3, 0, g+2n+5)
  have p1 : ⟨2*n+3, 0, 0, 3*n+3, 0, g+2⟩ [fm]⊢*
      ⟨0, 0, 2*n+3, 3*n+3, 0, g+2*n+5⟩ := by
    rw [show (2*n+3 : ℕ) = 0 + (2*n+3) from by omega,
        show (0 : ℕ) = 0 from rfl]
    apply stepStar_trans (r3_chain (2*n+3) 0 0 (3*n+3) (g+2))
    ring_nf; finish
  -- Phase 2: R4 × (3n+3): (0, 0, 2n+3, 3n+3, 0, g+2n+5) →* (0, 0, 2n+3, 0, 3n+3, g+2n+5)
  have p2 : ⟨0, 0, 2*n+3, 3*n+3, 0, g+2*n+5⟩ [fm]⊢*
      ⟨0, 0, 2*n+3, 0, 3*n+3, g+2*n+5⟩ := by
    rw [show (3*n+3 : ℕ) = 0 + (3*n+3) from by omega,
        show (0 : ℕ) = 0 + 0 from by omega]
    apply stepStar_trans (d_to_e (3*n+3) (2*n+3) 0 0 (g+2*n+5))
    ring_nf; finish
  -- Phase 3: R5 (one step): (0, 0, 2n+3, 0, 3n+3, g+2n+5) → (0, 2, 2n+3, 0, 3n+4, g+2n+4)
  have p3 : ⟨0, 0, 2*n+3, 0, 3*n+3, g+2*n+5⟩ [fm]⊢⁺
      ⟨0, 2, 2*n+3, 0, 3*n+4, g+2*n+4⟩ := by
    rw [show g+2*n+5 = (g+2*n+4) + 1 from by omega,
        show 3*n+4 = (3*n+3) + 1 from by omega]
    step fm; finish
  -- Phase 4: R1, R1: (0, 2, 2n+3, 0, 3n+4, g+2n+4) → (4, 0, 2n+1, 2, 3n+4, g+2n+4)
  have p4 : ⟨0, 2, 2*n+3, 0, 3*n+4, g+2*n+4⟩ [fm]⊢*
      ⟨4, 0, 2*n+1, 2, 3*n+4, g+2*n+4⟩ := by
    rw [show 2*n+3 = (2*n+1) + 1 + 1 from by omega]
    step fm; step fm; finish
  -- Phase 5: R2,R1 × (2n+1): (4, 0, 2n+1, 2, 3n+4, g+2n+4) →* (2n+5, 0, 0, 2n+3, n+3, g+2n+4)
  have p5 : ⟨4, 0, 2*n+1, 2, 3*n+4, g+2*n+4⟩ [fm]⊢*
      ⟨2*n+5, 0, 0, 2*n+3, n+3, g+2*n+4⟩ := by
    rw [show (4 : ℕ) = 3 + 1 from by omega,
        show 2*n+1 = 0 + (2*n+1) from by omega,
        show 3*n+4 = (n+3) + (2*n+1) from by omega]
    apply stepStar_trans (r2r1_chain (2*n+1) 3 0 2 (n+3) (g+2*n+4))
    ring_nf; finish
  -- Phase 6: R2 × (n+3): (2n+5, 0, 0, 2n+3, n+3, g+2n+4) →* (n+2, n+3, 0, 2n+3, 0, g+2n+4)
  have p6 : ⟨2*n+5, 0, 0, 2*n+3, n+3, g+2*n+4⟩ [fm]⊢*
      ⟨n+2, n+3, 0, 2*n+3, 0, g+2*n+4⟩ := by
    have h := r2_chain (n+3) (n+2) 0 (2*n+3) 0 (g+2*n+4)
    simp only [Nat.zero_add] at h
    rw [show 2*n+5 = n+2+(n+3) from by omega]
    exact h
  -- Phase 7: R3,R1 × (n+3): (n+2, n+3, 0, 2n+3, 0, g+2n+4) →* (2n+5, 0, 0, 3n+6, 0, g+3n+7)
  have p7 : ⟨n+2, n+3, 0, 2*n+3, 0, g+2*n+4⟩ [fm]⊢*
      ⟨2*n+5, 0, 0, 3*n+6, 0, g+3*n+7⟩ := by
    have h := r3r1_chain (n+3) (n+1) 0 (2*n+3) (g+2*n+4)
    simp only [Nat.zero_add] at h
    rw [show n+2 = n+1+1 from by omega] at p6 ⊢
    rw [show n+1+(n+3)+1 = 2*n+5 from by omega,
        show 2*n+3+(n+3) = 3*n+6 from by omega,
        show g+2*n+4+(n+3) = g+3*n+7 from by omega] at h
    exact h
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus p1
    (stepStar_stepPlus_stepPlus p2
      (stepPlus_stepStar_stepPlus p3
        (stepStar_trans p4
          (stepStar_trans p5
            (stepStar_trans p6 p7)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 3, 0, 2⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, g⟩ ↦ ⟨2*n+3, 0, 0, 3*n+3, 0, g+2⟩) ⟨0, 0⟩
  intro ⟨n, g⟩
  refine ⟨⟨n+1, g+3*n+5⟩, ?_⟩
  simp only []
  rw [show 2*(n+1)+3 = 2*n+5 from by ring,
      show 3*(n+1)+3 = 3*n+6 from by ring,
      show (g+3*n+5)+2 = g+3*n+7 from by ring]
  exact main_trans n g

end Sz22_2003_unofficial_517
