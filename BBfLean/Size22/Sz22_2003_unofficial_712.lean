import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #712: [35/6, 4/55, 121/2, 9/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  2  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_712

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem interleave : ∀ k, ∀ c d e, ⟨1, 2 * k, c, d, e + k⟩ [fm]⊢* ⟨1, 0, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem combined_drain : ∀ c, ∀ a D E, ⟨a + 1, 0, c, D, E⟩ [fm]⊢* ⟨0, 0, 0, D, 2 * a + 2 + E + 3 * c⟩ := by
  intro c; induction' c with c ih <;> intro a D E
  · rw [show 2 * a + 2 + E + 3 * 0 = E + 2 * (a + 1) from by ring]
    have h := r3_chain (a + 1) 0 D E
    convert h using 2; ring_nf
  · rcases E with _ | E
    · step fm
      rw [show c + 1 = (c + 1) from rfl]
      step fm
      apply stepStar_trans (ih (a + 1) D 1)
      ring_nf; finish
    · rw [show c + 1 = c + 1 from rfl,
          show E + 1 = E + 1 from rfl]
      step fm
      apply stepStar_trans (ih (a + 2) D E)
      ring_nf; finish

theorem main_trans (d e : ℕ) :
    ⟨0, 0, 0, d + 1, e + d + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 3, e + 3 * d + 6⟩ := by
  rw [show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d + 1) 0 0 (e + d + 3))
  rw [show 0 + 2 * (d + 1) = 2 * (d + 1) from by ring]
  rw [show e + d + 3 = (e + 1) + (d + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * (d + 1), 0, 0, (e + 1) + (d + 1) + 1⟩ = some ⟨1, 2 * (d + 1), 0, 1, (e + 1) + (d + 1)⟩
    simp [fm]
  rw [show (e + 1) + (d + 1) = (e + 1) + (d + 1) from rfl]
  apply stepStar_trans (interleave (d + 1) 0 1 (e + 1))
  rw [show 0 + (d + 1) = d + 1 from by ring,
      show 1 + 2 * (d + 1) = 2 * d + 3 from by ring]
  apply stepStar_trans (combined_drain (d + 1) 0 (2 * d + 3) (e + 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 1, e + d + 3⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  refine ⟨⟨2 * d + 2, e + d + 1⟩, ?_⟩
  have h := main_trans d e
  convert h using 2; ring_nf

end Sz22_2003_unofficial_712
