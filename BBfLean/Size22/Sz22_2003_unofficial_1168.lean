import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1168: [5/6, 441/55, 121/3, 2/7, 15/2]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1  2 -1
 0 -1  0  0  2
 1  0  0 -1  0
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1168

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+2, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: (a, 0, 0, d+k, e) →* (a+k, 0, 0, d, e)
theorem r4_chain : ∀ k, ∀ a d e, ⟨a, 0, 0, d + k, e⟩ [fm]⊢* ⟨a + k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) d e)
    ring_nf; finish

-- R3 chain: (0, b+k, 0, d, e) →* (0, b, 0, d, e+2*k)
theorem r3_chain : ∀ k, ∀ b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 2))
    ring_nf; finish

-- R2 chain: (0, b, c+k, d, e+k) →* (0, b+2*k, c, d+2*k, e)
theorem r2_chain : ∀ k, ∀ b c d e, ⟨0, b, c + k, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) c (d + 2) e)
    ring_nf; finish

-- R2 step with symbolic first component: (a, 0, c+1, d, e+1) → (a, 2, c, d+2, e)
theorem r2_step : ∀ a c d e, ⟨a, 0, c + 1, d, e + 1⟩ [fm]⊢ ⟨a, 2, c, d + 2, e⟩ := by
  intro a c d e; simp [fm]

-- R1+R1+R2 interleaving: (a+a, 2, c, d, e+a) →* (0, 2, c+a, d+a+a, e)
theorem r1r1r2_chain : ∀ a, ∀ c d e,
    ⟨a + a, 2, c, d, e + a⟩ [fm]⊢* ⟨0, 2, c + a, d + a + a, e⟩ := by
  intro a; induction' a with a ih <;> intro c d e
  · exists 0
  · rw [show (a + 1) + (a + 1) = (a + a + 1) + 1 from by ring,
        show e + (a + 1) = (e + a) + 1 from by ring]
    step fm  -- R1
    step fm  -- R1
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring]
    apply stepStar_trans (step_stepStar (r2_step (a + a) (c + 1) d (e + a)))
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

-- Opening: R5+R1+R2 from (a+2, 0, 0, 0, e+2) →⁺ (a, 2, 1, 2, e+1)
theorem opening : ∀ a e, ⟨a + 2, 0, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨a, 2, 1, 2, e + 1⟩ := by
  intro a e
  rw [show a + 2 = (a + 1) + 1 from by ring]
  step fm  -- R5
  step fm  -- R1
  rw [show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (step_stepStar (r2_step a 1 0 (e + 1)))
  ring_nf; finish

-- Main transition: (m+m+2, 0, 0, 0, f+m+m+2) →⁺ (m+m+m+m+4, 0, 0, 0, f+m+m+m+m+8)
theorem main_transition : ∀ m f,
    ⟨m + m + 2, 0, 0, 0, f + m + m + 2⟩ [fm]⊢⁺
    ⟨m + m + m + m + 4, 0, 0, 0, f + m + m + m + m + 8⟩ := by
  intro m f
  rw [show m + m + 2 = (m + m) + 2 from by ring,
      show f + m + m + 2 = f + (m + m) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (m + m) (f + (m + m)))
  rw [show f + (m + m) + 1 = (f + m + 1) + m from by ring]
  apply stepStar_trans (r1r1r2_chain m 1 2 (f + m + 1))
  rw [show 1 + m = 0 + (m + 1) from by ring,
      show f + m + 1 = f + (m + 1) from by ring,
      show 2 + m + m = m + m + 2 from by ring]
  apply stepStar_trans (r2_chain (m + 1) 2 0 (m + m + 2) f)
  rw [show 2 + 2 * (m + 1) = 0 + (m + m + 4) from by ring,
      show m + m + 2 + 2 * (m + 1) = m + m + m + m + 4 from by ring]
  apply stepStar_trans (r3_chain (m + m + 4) 0 (m + m + m + m + 4) f)
  rw [show f + 2 * (m + m + 4) = f + m + m + m + m + 8 from by ring,
      show (m + m + m + m + 4 : ℕ) = 0 + (m + m + m + m + 4) from by ring]
  exact r4_chain (m + m + m + m + 4) 0 0 (f + m + m + m + m + 8)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 5⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m f, q = ⟨m + m + 2, 0, 0, 0, f + m + m + 2⟩)
  · intro c ⟨m, f, hq⟩; subst hq
    exact ⟨⟨m + m + m + m + 4, 0, 0, 0, f + m + m + m + m + 8⟩,
      ⟨m + m + 1, f + 4, by ring_nf⟩,
      main_transition m f⟩
  · exact ⟨0, 3, by ring_nf⟩
