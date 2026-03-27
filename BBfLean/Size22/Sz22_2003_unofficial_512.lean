import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #512: [28/15, 3/22, 65/2, 11/7, 21/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_512

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R3 chain: drain a, build c and f
theorem a_to_cf : ∀ k c d f, ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by omega]
  step fm
  apply stepStar_trans (ih (c + 1) d (f + 1))
  ring_nf; finish

-- R4 chain: drain d, build e
theorem d_to_e : ∀ k c d e f, ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by omega]
  step fm
  apply stepStar_trans (ih c d (e + 1) f)
  ring_nf; finish

-- R2R1 chain: interleaved R2, R1 with a=d invariant
theorem r2r1_chain : ∀ k a c e f, ⟨a+2, 0, c+k, a+2, e+k, f⟩ [fm]⊢* ⟨a+k+2, 0, c, a+k+2, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by omega,
      show e + (k + 1) = (e + k) + 1 from by omega,
      show a + 2 = (a + 1) + 1 from by omega]
  step fm; step fm
  apply stepStar_trans (ih (a + 1) c e f)
  ring_nf; finish

-- R2 chain: drain e, build b
theorem e_to_b : ∀ k a b d f, ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+k, 0, d, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by omega]
  step fm
  apply stepStar_trans (ih a (b + 1) d f)
  ring_nf; finish

-- R3R1 chain: interleaved R3, R1
theorem r3r1_chain : ∀ k a b d f, ⟨a+1, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+k+1, b, 0, d+k, 0, f+k⟩ := by
  intro k; induction' k with k ih <;> intro a b d f
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by omega]
  step fm; step fm
  apply stepStar_trans (ih (a + 1) b (d + 1) (f + 1))
  ring_nf; finish

-- Main transition: C(n) →⁺ C(n+1) where C(n) = (n+2, 0, 0, 2n+2, 0, n(n+1))
theorem main_trans (n : ℕ) :
    ⟨n+2, 0, 0, 2*n+2, 0, n*(n+1)⟩ [fm]⊢⁺ ⟨n+3, 0, 0, 2*n+4, 0, (n+1)*(n+2)⟩ := by
  -- Phase 1: R3 chain (n+2 steps): drain a to c and f
  have p1 : ⟨n+2, 0, 0, 2*n+2, 0, n*(n+1)⟩ [fm]⊢*
      ⟨0, 0, n+2, 2*n+2, 0, n*(n+1)+(n+2)⟩ := by
    have h := a_to_cf (a := 0) (n+2) 0 (2*n+2) (n*(n+1))
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 chain (2n+2 steps): drain d to e
  have p2 : ⟨0, 0, n+2, 2*n+2, 0, n*(n+1)+(n+2)⟩ [fm]⊢*
      ⟨0, 0, n+2, 0, 2*n+2, n*(n+1)+(n+2)⟩ := by
    have h := d_to_e (2*n+2) (n+2) 0 0 (n*(n+1)+(n+2))
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5 + R1 (2 steps, gives ⊢⁺)
  have p3 : ⟨0, 0, n+2, 0, 2*n+2, n*(n+1)+(n+2)⟩ [fm]⊢⁺
      ⟨2, 0, n+1, 2, 2*n+2, n*(n+1)+(n+1)⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by omega,
        show n * (n + 1) + (n + 2) = (n * (n + 1) + (n + 1)) + 1 from by omega]
    step fm; step fm; finish
  -- Phase 4: R2R1 chain (n+1 pairs)
  have p4 : ⟨2, 0, n+1, 2, 2*n+2, n*(n+1)+(n+1)⟩ [fm]⊢*
      ⟨n+3, 0, 0, n+3, n+1, n*(n+1)+(n+1)⟩ := by
    have h := r2r1_chain (n+1) 0 0 (n+1) (n*(n+1)+(n+1))
    simp only [Nat.zero_add] at h
    rw [show n + 1 + (n + 1) = 2 * n + 2 from by omega,
        show n + 1 + 2 = n + 3 from by omega] at h
    exact h
  -- Phase 5: R2 drain (n+1 steps)
  have p5 : ⟨n+3, 0, 0, n+3, n+1, n*(n+1)+(n+1)⟩ [fm]⊢*
      ⟨2, n+1, 0, n+3, 0, n*(n+1)+(n+1)⟩ := by
    rw [show n + 3 = 2 + (n + 1) from by omega]
    have h := e_to_b (n+1) 2 0 (2 + (n + 1)) (n*(n+1)+(n+1))
    simp only [Nat.zero_add] at h; exact h
  -- Phase 6: R3R1 chain (n+1 pairs)
  have p6 : ⟨2, n+1, 0, n+3, 0, n*(n+1)+(n+1)⟩ [fm]⊢*
      ⟨n+3, 0, 0, 2*n+4, 0, (n+1)*(n+2)⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by omega]
    have h := r3r1_chain (n+1) 1 0 (n+3) (n*(n+1)+(n+1))
    simp only [Nat.zero_add] at h
    rw [show 1 + (n + 1) + 1 = n + 3 from by omega,
        show n + 3 + (n + 1) = 2 * n + 4 from by omega,
        show n * (n + 1) + (n + 1) + (n + 1) = (n + 1) * (n + 2) from by ring] at h
    exact h
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus p1
    (stepStar_stepPlus_stepPlus p2
      (stepPlus_stepStar_stepPlus (stepPlus_stepStar_stepPlus
        (stepPlus_stepStar_stepPlus p3 p4) p5) p6))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n+2, 0, 0, 2*n+2, 0, n*(n+1)⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩

end Sz22_2003_unofficial_512
