import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #701: [35/6, 4/55, 121/2, 3/7, 175/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  2  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_701

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem interleave : ∀ b, ∀ c d E, ⟨2, b, c + 1, d, E + b + c + 1⟩ [fm]⊢* ⟨b + 2 * c + 4, 0, 0, d + b, E⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c d E
  rcases b with _ | _ | b
  · -- b = 0
    simp only [Nat.zero_add, Nat.add_zero]
    rw [show c + 1 = 0 + (c + 1) from by ring]
    apply stepStar_trans (r2_chain (c + 1) 2 0 d E)
    ring_nf; finish
  · -- b = 1
    rw [show E + 1 + c + 1 = (E + c + 1) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show c + 1 + 1 = 0 + (c + 2) from by ring,
        show E + c + 1 + 1 = E + (c + 2) from by ring]
    apply stepStar_trans (r2_chain (c + 2) 1 0 (d + 1) E)
    ring_nf; finish
  · -- b = b + 2
    rw [show E + (b + 2) + c + 1 = (E + b + c + 2) + 1 from by ring]
    step fm
    rw [show (b + 2 : ℕ) = (b + 1) + 1 from by ring]
    step fm
    rw [show E + b + c + 2 = (E + b + c + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (by omega) (c + 1) (d + 2) E)
    ring_nf; finish

theorem main_trans (d E : ℕ) :
    ⟨0, 0, 0, d + 1, E + d + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 2, E + 2 * d + 10⟩ := by
  have phase1 : ⟨0, 0, 0, d + 1, E + d + 4⟩ [fm]⊢* ⟨0, d + 1, 0, 0, E + d + 4⟩ := by
    rw [show d + 1 = 0 + (d + 1) from by ring]
    exact r4_chain (d + 1) 0 0 (E + d + 4)
  have phase2 : ⟨0, d + 1, 0, 0, E + d + 4⟩ [fm]⊢⁺ ⟨0, d + 1, 2, 1, E + d + 3⟩ := by
    rw [show E + d + 4 = (E + d + 3) + 1 from by ring]
    step fm; finish
  have phase3 : ⟨0, d + 1, 2, 1, E + d + 3⟩ [fm]⊢* ⟨2, d + 1, 1, 1, E + d + 2⟩ := by
    rw [show E + d + 3 = (E + d + 2) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm; finish
  have phase4 : ⟨2, d + 1, 1, 1, E + d + 2⟩ [fm]⊢* ⟨d + 5, 0, 0, d + 2, E⟩ := by
    rw [show E + d + 2 = E + (d + 1) + 0 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (interleave (d + 1) 0 1 E)
    ring_nf; finish
  have phase5 : ⟨d + 5, 0, 0, d + 2, E⟩ [fm]⊢* ⟨0, 0, 0, d + 2, E + 2 * d + 10⟩ := by
    rw [show d + 5 = 0 + (d + 5) from by ring,
        show E + 2 * d + 10 = E + 2 * (d + 5) from by ring]
    exact r3_chain (d + 5) 0 (d + 2) E
  exact stepStar_stepPlus_stepPlus phase1
    (stepPlus_stepStar_stepPlus phase2
      (stepStar_trans phase3
        (stepStar_trans phase4 phase5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 7⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, E⟩ ↦ ⟨0, 0, 0, d + 1, E + d + 4⟩) ⟨0, 3⟩
  intro ⟨d, E⟩
  refine ⟨⟨d + 1, E + d + 5⟩, ?_⟩
  show ⟨0, 0, 0, d + 1, E + d + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 1 + 1, E + d + 5 + (d + 1) + 4⟩
  rw [show d + 1 + 1 = d + 2 from by ring,
      show E + d + 5 + (d + 1) + 4 = E + 2 * d + 10 from by ring]
  exact main_trans d E

end Sz22_2003_unofficial_701
