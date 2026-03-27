import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #513: [28/15, 3/22, 65/2, 11/7, 242/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  1  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 1  0  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_513

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e+2, f⟩
  | _ => none

-- R3 repeated: (a+k, 0, c, d, 0, f) →* (a, 0, c+k, d, 0, f+k)
theorem a_to_cf : ∀ k, ∀ a c d f, ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d f
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _ _); ring_nf; finish

-- R4 repeated: (0, 0, c, d+k, e, f) →* (0, 0, c, d, e+k, f)
theorem d_to_e : ∀ k, ∀ c d e f, ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _ _); ring_nf; finish

-- (R2, R1) chain: (A+1, 0, k, D, E+k, F) →* (A+1+k, 0, 0, D+k, E, F)
theorem r2r1_chain : ∀ k, ∀ A D E F, ⟨A+1, 0, k, D, E+k, F⟩ [fm]⊢* ⟨A+1+k, 0, 0, D+k, E, F⟩ := by
  intro k; induction' k with k ih <;> intro A D E F
  · exists 0
  -- State: (A+1, 0, k+1, D, E+k+1, F)
  -- R2 fires: a=A+1≥1, e=E+k+1≥1 → (A, 1, k+1, D, E+k, F)
  -- R1 fires: b=1≥1, c=k+1≥1 → (A+2, 0, k, D+1, E+k, F)
  step fm
  rw [show k + 1 = k + 1 from rfl]
  step fm
  rw [show A + 1 + 1 = (A + 1) + 1 from by ring]
  apply stepStar_trans (ih (A + 1) (D + 1) E F)
  ring_nf; finish

-- R2 repeated with c=0: (A+k, B, 0, D, k, F) →* (A, B+k, 0, D, 0, F)
theorem e_to_b : ∀ k, ∀ A B D F, ⟨A+k, B, 0, D, k, F⟩ [fm]⊢* ⟨A, B+k, 0, D, 0, F⟩ := by
  intro k; induction' k with k ih <;> intro A B D F
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (ih _ _ _ _); ring_nf; finish

-- (R3, R1) chain: (A+1, B+k, 0, D, 0, F) →* (A+1+k, B, 0, D+k, 0, F+k)
theorem r3r1_chain : ∀ k, ∀ A B D F, ⟨A+1, B+k, 0, D, 0, F⟩ [fm]⊢* ⟨A+1+k, B, 0, D+k, 0, F+k⟩ := by
  intro k; induction' k with k ih <;> intro A B D F
  · exists 0
  -- State: (A+1, B+k+1, 0, D, 0, F)
  -- R1 needs c≥1, c=0: no. R2 needs e≥1, e=0: no. R3 fires: a=A+1≥1.
  -- R3: (A, B+k+1, 1, D, 0, F+1)
  -- R1: b=B+k+1≥1, c=1≥1 → (A+2, B+k, 0, D+1, 0, F+1)
  step fm
  rw [show k + 1 = k + 1 from rfl]
  step fm
  rw [show A + 1 + 1 = (A + 1) + 1 from by ring]
  apply stepStar_trans (ih (A + 1) B (D + 1) (F + 1))
  ring_nf; finish

-- Main transition: canonical(n) →⁺ canonical(n+1)
theorem main_trans (n : ℕ) :
    (⟨n+1, 0, 0, 2*n, 0, n*n⟩ : Q) [fm]⊢⁺ ⟨n+2, 0, 0, 2*n+2, 0, (n+1)*(n+1)⟩ := by
  -- Phase 1: R3 x (n+1): → (0, 0, n+1, 2n, 0, n*n+n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, 2*n, 0, n*n+(n+1)⟩)
  · have h := a_to_cf (n+1) 0 0 (2*n) (n*n)
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 x (2n): → (0, 0, n+1, 0, 2n, n*n+n+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, n+1, 0, 2*n, n*n+(n+1)⟩)
  · have h := d_to_e (2*n) (n+1) 0 0 (n*n+(n+1))
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3a: R5 once: → (1, 0, n+1, 0, 2n+2, n*n+n)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, n+1, 0, 2*n+2, n*n+n⟩)
  · show fm ⟨0, 0, n+1, 0, 2*n, (n*n+n)+1⟩ = some ⟨1, 0, n+1, 0, 2*n+2, n*n+n⟩
    simp [fm]
  -- Phase 3b: (R2, R1) x (n+1): → (n+2, 0, 0, n+1, n+1, n*n+n)
  apply stepStar_trans (c₂ := ⟨n+2, 0, 0, n+1, n+1, n*n+n⟩)
  · have h := r2r1_chain (n+1) 0 0 (n+1) (n*n+n)
    simp only [Nat.zero_add] at h
    rw [show (0 : ℕ) + 1 + (n + 1) = n + 2 from by ring] at h
    convert h using 2; ring_nf
  -- Phase 3c: R2 x (n+1): → (1, n+1, 0, n+1, 0, n*n+n)
  apply stepStar_trans (c₂ := ⟨1, n+1, 0, n+1, 0, n*n+n⟩)
  · have h := e_to_b (n+1) 1 0 (n+1) (n*n+n)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 4: (R3, R1) x (n+1): → (n+2, 0, 0, 2n+2, 0, (n+1)²)
  have h := r3r1_chain (n+1) 0 0 (n+1) (n*n+n)
  simp only [Nat.zero_add] at h
  rw [show (0 : ℕ) + 1 + (n + 1) = n + 2 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 2*n, 0, n*n⟩) 0
  intro n; exact ⟨n+1, main_trans n⟩

end Sz22_2003_unofficial_513
