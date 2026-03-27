import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #591: [35/6, 121/2, 28/55, 3/7, 25/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  1 -1
 0  1  0 -1  0
 0  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_591

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _)
    ring_nf; finish
  exact many_step k b

-- R3,R1,R1 chain
theorem r3r1r1_chain : ∀ k, ∀ b c d e,
    ⟨0, b+2*k, c+1, d, e+1+k⟩ [fm]⊢* ⟨0, b, c+1+k, d+3*k, e+1⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
      show e + 1 + (k + 1) = (e + k + 1) + 1 from by ring,
      show c + 1 + (k + 1) = (c + 1 + 1) + k from by ring,
      show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring]
  step fm
  rw [show (b + 2) + 2 * k = (b + 2 * k + 1) + 1 from by ring]
  step fm
  rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
  step fm
  rw [show e + k + 1 = e + 1 + k from by ring]
  apply stepStar_trans (h b (c + 1) (d + 1 + 1 + 1) e)
  ring_nf; finish

-- R3,R2,R2 chain
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d+k, e+3*k+1⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + 1) + k from by ring,
      show e + 3 * (k + 1) + 1 = (e + 3) + 3 * k + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + 4 = (e + 3) + 1 from by ring]
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition
theorem main_trans : ⟨0, 0, 0, 2*d, e+d+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*d+2, e+3*d+7⟩ := by
  -- Phase 1: d_to_b
  rw [show (2 : ℕ) * d = 0 + 2 * d from by ring]
  apply stepStar_stepPlus_stepPlus (@d_to_b 0 0 (2*d) (e+d+2))
  simp only [Nat.zero_add]
  -- Phase 2: R5
  rw [show e + d + 2 = (e + d + 1) + 1 from by ring]
  step fm
  -- Phase 3: r3r1r1_chain
  rw [show e + d + 1 = e + 1 + d from by ring]
  show (⟨0, 2 * d, 1 + 1, 0, e + 1 + d⟩ : Q) [fm]⊢* ⟨0, 0, 0, 4 * d + 2, e + 3 * d + 7⟩
  have h3 := r3r1r1_chain d 0 1 0 e
  simp only [Nat.zero_add] at h3
  refine stepStar_trans h3 ?_
  -- Phase 4: r3r2r2_chain
  rw [show (1 : ℕ) + 1 + d = 0 + (d + 2) from by ring]
  refine stepStar_trans (r3r2r2_chain (d + 2) 0 (3 * d) e) ?_
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, 2*d, e+d+2⟩)
  · intro c ⟨d, e, hq⟩; subst hq
    refine ⟨⟨0, 0, 0, 4*d+2, e+3*d+7⟩, ⟨2*d+1, e+d+4, ?_⟩, main_trans⟩
    show (0, 0, 0, 4*d+2, e+3*d+7) = (0, 0, 0, 2*(2*d+1), e+d+4+(2*d+1)+2)
    ring_nf
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_591
