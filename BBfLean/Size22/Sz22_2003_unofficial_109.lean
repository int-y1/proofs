import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #109: [1/30, 6/77, 196/3, 5/7, 33/2]

Vector representation:
```
-1 -1 -1  0  0
 1  1  0 -1 -1
 2 -1  0  2  0
 0  0  1 -1  0
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_109

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 repeated: d → c
theorem d_to_c : ∀ k a c d, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, (0 : ℕ), c + k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5,R1 chain
theorem r5r1_chain : ∀ k a c e, ⟨a + 2 * k, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, (0 : ℕ), c, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    rw [show e + (k + 1) = (e + 1) + k from by ring]
    exact ih a c (e + 1)

-- R3 repeated: b → a,d
theorem b_to_ad : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, (0 : ℕ), d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d; exists 0
  | succ k ih =>
    intro a d
    show ⟨a, (k) + 1, 0, d, 0⟩ [fm]⊢* _
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase 4 with b >= 1
theorem phase4_pos : ∀ k, ∀ b a,
    ⟨a, b + 1, 0, 2, k⟩ [fm]⊢* ⟨a + 3 * k + 2 * b + 2, 0, (0 : ℕ), k + 2 * b + 4, 0⟩ := by
  intro k; induction' k using Nat.strongRecOn with k ih; intro b a
  rcases k with _ | _ | k
  · -- k = 0
    apply stepStar_trans (b_to_ad (b + 1) a 2)
    ring_nf; finish
  · -- k = 1
    rw [show (2 : ℕ) = 1 + 1 from by ring, show (0 + 1 : ℕ) = 0 + 1 from by ring]
    step fm
    show ⟨a + 1, b + 1 + 1, 0, 1, 0⟩ [fm]⊢* _
    step fm
    show ⟨a + 1 + 2, b + 1, 0, 1 + 2, 0⟩ [fm]⊢* _
    apply stepStar_trans (b_to_ad (b + 1) (a + 1 + 2) (1 + 2))
    ring_nf; finish
  · -- k + 2
    rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    show ⟨a + 1, b + 1 + 1, 0, 1, k + 1⟩ [fm]⊢* _
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    show ⟨a + 1 + 1, b + 1 + 1 + 1, 0, 0, k⟩ [fm]⊢* _
    rw [show b + 1 + 1 + 1 = (b + 2) + 1 from by ring]
    step fm
    show ⟨a + 1 + 1 + 2, b + 2, 0, 0 + 2, k⟩ [fm]⊢* _
    rw [show (0 : ℕ) + 2 = 2 from by ring,
        show b + 2 = (b + 1) + 1 from by ring,
        show a + 1 + 1 + 2 = a + 4 from by ring]
    apply stepStar_trans (ih k (by omega) (b + 1) (a + 4))
    ring_nf; finish

-- Phase 4 with b=0
theorem phase4 : ∀ k a,
    ⟨a, 0, 0, 2, k + 1⟩ [fm]⊢* ⟨a + 3 * k + 3, 0, (0 : ℕ), k + 3, 0⟩ := by
  intro k a
  rcases k with _ | k
  · -- k = 0
    rw [show (2 : ℕ) = 1 + 1 from by ring, show (0 + 1 : ℕ) = 0 + 1 from by ring]
    step fm
    show ⟨a + 1, 0 + 1, 0, 1, 0⟩ [fm]⊢* _
    step fm
    show ⟨a + 1 + 2, 0, 0, 1 + 2, 0⟩ [fm]⊢* _
    ring_nf; finish
  · -- k + 1
    rw [show (k + 1 + 1 : ℕ) = (k + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    show ⟨a + 1, 0 + 1, 0, 1, k + 1⟩ [fm]⊢* _
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    show ⟨a + 1 + 1, 0 + 1 + 1, 0, 0, k⟩ [fm]⊢* _
    rw [show (0 : ℕ) + 1 + 1 = 1 + 1 from by ring]
    step fm
    show ⟨a + 1 + 1 + 2, 1, 0, 0 + 2, k⟩ [fm]⊢* _
    rw [show (0 : ℕ) + 2 = 2 from by ring,
        show a + 1 + 1 + 2 = a + 4 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (phase4_pos k 0 (a + 4))
    ring_nf; finish

-- Main transition
theorem main_step : ∀ d x,
    ⟨x + 2 * d + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨x + 3 * d + 5, 0, (0 : ℕ), d + 3, 0⟩ := by
  intro d x
  apply stepStar_stepPlus_stepPlus
  · -- Phase 1
    have h := d_to_c d (x + 2 * d + 1) 0 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · -- Phase 2
    have h := r5r1_chain d (x + 1) 0 0
    simp only [Nat.zero_add] at h
    rw [show (x + 1) + 2 * d = x + 2 * d + 1 from by ring] at h; exact h
  -- Phase 3: R5, R3
  apply step_stepStar_stepPlus
  · show fm ⟨x + 1, 0, 0, 0, d⟩ = some ⟨x, 1, 0, 0, d + 1⟩
    unfold fm; simp
  show ⟨x, 1, 0, 0, d + 1⟩ [fm]⊢* ⟨x + 3 * d + 5, 0, (0 : ℕ), d + 3, 0⟩
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  show ⟨x + 2, 0, 0, 0 + 2, d + 1⟩ [fm]⊢* _
  rw [show (0 : ℕ) + 2 = 2 from by ring]
  -- Phase 4
  apply stepStar_trans (phase4 d (x + 2))
  ring_nf; finish

-- Bootstrap
theorem bootstrap : c₀ [fm]⊢* ⟨8, 0, (0 : ℕ), 3, 0⟩ := by
  unfold c₀; execute fm 19

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts bootstrap
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ x d, q = ⟨x + 2 * d + 1, 0, (0 : ℕ), d, 0⟩ ∧ d ≥ 2)
  · intro q ⟨x, d, hq, hd⟩
    subst hq
    obtain ⟨w, hw⟩ : ∃ w, x + d = w + 2 := ⟨x + d - 2, by omega⟩
    refine ⟨⟨x + 3 * d + 5, 0, (0 : ℕ), d + 3, 0⟩,
            ⟨w, d + 3, ?_, by omega⟩,
            main_step d x⟩
    congr 1; omega
  · exact ⟨1, 3, rfl, by omega⟩

end Sz22_2003_unofficial_109
