import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #633: [35/6, 143/2, 4/55, 3/7, 245/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  0  1  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_633

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d+2, e, f⟩
  | _ => none

-- R4 repeated: transfer d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- (R1,R1,R3) repeated: consume b in pairs, transfer to c and d
theorem r1r1r3_chain : ∀ k, ∀ c d e,
    ⟨2, b+2*k, c, d, e+k, f⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e, f⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- (R2,R2,R3) repeated: drain c, accumulate e and f
theorem r2r2r3_chain : ∀ k, ∀ c e f,
    ⟨2, 0, c+k, d, e, f⟩ [fm]⊢* ⟨2, 0, c, d, e+k, f+2*k⟩ := by
  intro k; induction' k with k h <;> intro c e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Combined transition from canonical state to next
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2*n, n+1, n*n+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*(n+1), (n+1)+1, (n+1)*(n+1)+1⟩ := by
  -- Phase 1: R4 x 2n → (0, 2n, 0, 0, n+1, n²+1)
  have h1 : ⟨0, 0, 0, 0+2*n, n+1, n*n+1⟩ [fm]⊢* ⟨0, 0+2*n, 0, 0, n+1, n*n+1⟩ :=
    d_to_b (d := 0) (e := n+1) (f := n*n+1) (2*n) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2+3: R5, R3 → (2, 2*n, 0, 2, n, n*n)
  rw [show n*n+1 = n*n + 1 from by ring]
  step fm; step fm
  -- Phase 4: (R1,R1,R3) x n → (2, 0, n, 2+2*n, 0, n*n)
  have h4 : ⟨2, 0+2*n, 0, 2, 0+n, n*n⟩ [fm]⊢* ⟨2, 0, 0+n, 2+2*n, 0, n*n⟩ :=
    r1r1r3_chain (b := 0) (f := n*n) n 0 2 0
  simp only [Nat.zero_add] at h4
  apply stepStar_trans h4
  -- Phase 5: (R2,R2,R3) x n → (2, 0, 0, 2+2*n, n, n*n+2*n)
  have h5 : ⟨2, 0, 0+n, 2+2*n, 0, n*n⟩ [fm]⊢* ⟨2, 0, 0, 2+2*n, 0+n, n*n+2*n⟩ :=
    r2r2r3_chain (d := 2+2*n) n 0 0 (n*n)
  simp only [Nat.zero_add] at h5
  apply stepStar_trans h5
  -- Phase 6: R2, R2
  step fm; step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2*n, n+1, n*n+1⟩) 1
  intro n; exists n+1; exact main_trans n

end Sz22_2003_unofficial_633
