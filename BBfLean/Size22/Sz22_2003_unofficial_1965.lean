import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1965: [99/35, 10/3, 1/5, 49/2, 1/77, 5/7]

Vector representation:
```
 0  2 -1 -1  1
 1 -1  1  0  0
 0  0 -1  0  0
-1  0  0  2  0
 0  0  0 -1 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1965

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- Phase 2: R1+R2 interleaving. (a, b, 1, D+k, e) ->* (a+k, b+k, 1, D, e+k)
theorem r1r2_chain : ∀ k, ∀ a b D e, ⟨a, b, 1, D + k, e⟩ [fm]⊢* ⟨a + k, b + k, 1, D, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b D e
  · exists 0
  · rw [show D + (k + 1) = (D + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (a + 1) (b + 1) D (e + 1))
    ring_nf; finish

-- Phase 3: R2 drain b. (a, b+k, c, 0, e) ->* (a+k, b, c+k, 0, e)
theorem r2_drain : ∀ k, ∀ a b c e, ⟨a, b + k, c, 0, e⟩ [fm]⊢* ⟨a + k, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (c + 1) e)
    ring_nf; finish

-- Phase 4: R3 drain c. (a, 0, c+k, 0, e) ->* (a, 0, c, 0, e)
theorem r3_drain : ∀ k, ∀ a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c e)
    finish

-- Phase 5: R4 drain a. (a+k, 0, 0, d, e) ->* (a, 0, 0, d+2*k, e)
theorem r4_drain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) e)
    ring_nf; finish

-- Phase 6: R5 drain min(d,e). (0, 0, 0, d+k, e+k) ->* (0, 0, 0, d, e)
theorem r5_drain : ∀ k, ∀ d e, ⟨0, 0, 0, d + k, e + k⟩ [fm]⊢* ⟨0, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d e)
    finish

-- Full transition from (0,0,0,D+2,0): combines all phases
theorem full_trans : ∀ D, ⟨0, 0, 1, D, 0⟩ [fm]⊢* ⟨D, D, 1, 0, D⟩ := by
  intro D
  have h := r1r2_chain D 0 0 0 0
  simp only [Nat.zero_add] at h
  exact h

theorem main_trans : ∀ d, ⟨0, 0, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 3 * d + 3, 0⟩ := by
  intro d
  step fm
  apply stepStar_trans (full_trans (d + 1))
  have h2 : ⟨d + 1, d + 1, 1, 0, d + 1⟩ [fm]⊢* ⟨2 * d + 2, 0, d + 2, 0, d + 1⟩ := by
    have h := r2_drain (d + 1) (d + 1) 0 1 (d + 1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  apply stepStar_trans h2
  have h3 : ⟨2 * d + 2, 0, d + 2, 0, d + 1⟩ [fm]⊢* ⟨2 * d + 2, 0, 0, 0, d + 1⟩ := by
    have h := r3_drain (d + 2) (2 * d + 2) 0 (d + 1)
    simp only [Nat.zero_add] at h
    exact h
  apply stepStar_trans h3
  have h4 : ⟨2 * d + 2, 0, 0, 0, d + 1⟩ [fm]⊢* ⟨0, 0, 0, 4 * d + 4, d + 1⟩ := by
    have h := r4_drain (2 * d + 2) 0 0 (d + 1)
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish
  apply stepStar_trans h4
  have h5 : ⟨0, 0, 0, 4 * d + 4, d + 1⟩ [fm]⊢* ⟨0, 0, 0, 3 * d + 3, 0⟩ := by
    have h := r5_drain (d + 1) (3 * d + 3) 0
    simp only [Nat.zero_add] at h
    rw [show 4 * d + 4 = (3 * d + 3) + (d + 1) from by ring]
    exact h
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨0, 0, 0, d + 2, 0⟩) 0
  intro d; exists 3 * d + 1; exact main_trans d
