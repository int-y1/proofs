import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #631: [35/6, 143/2, 4/55, 3/7, 175/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  0  2  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_631

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+2, d+1, e, f⟩
  | _ => none

-- R4 repeated: transfer d to b
theorem d_to_b : ∀ k b, ⟨(0 : ℕ), b, 0, 0+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b
  · exists 0
  rw [show 0 + (k + 1) = (0 + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih _); ring_nf; finish

-- R3+R2+R2 drain
theorem r3r2r2_drain : ∀ k, ∀ c e f, ⟨(0 : ℕ), 0, c+k+1, d, e+k+1, f⟩ [fm]⊢*
    ⟨0, 0, c+1, d, e+2*k+1, f+2*k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  rw [show c + (k + 1) + 1 = (c + k + 1) + 1 from by ring,
      show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
  step fm; step fm; step fm
  rw [show c + k + 1 = c + k + 1 from rfl,
      show e + k + 1 + 1 + 1 = (e + 2) + k + 1 from by ring,
      show f + 1 + 1 = f + 2 from by ring]
  apply stepStar_trans (ih c (e + 2) (f + 2))
  ring_nf; finish

-- R3+R1+R1 chain
theorem r3r1r1_chain : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), b+2*k, c+1, d, e+k+1, f⟩ [fm]⊢* ⟨0, b, c+k+1, d+2*k, e+1, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
  step fm; step fm; step fm
  rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
      show d + 1 + 1 = (d + 2) from by ring]
  apply stepStar_trans (ih (c + 1) (d + 2) e)
  ring_nf; finish

-- Chain + drain for even case: from after R4+R5+R3+R1+R1 opening
theorem even_body : ⟨0, 2*m, 2+1, 3, 4*m+4, f⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+3, 4*m+7, f+2*m+6⟩ := by
  rw [show (4*m+4 : ℕ) = (3*m+3)+m+1 from by ring,
      show (2*m : ℕ) = 0+2*m from by ring]
  apply stepStar_stepPlus_stepPlus (r3r1r1_chain (b := 0) (f := f) m 2 3 (3*m+3))
  rw [show 2+m+1 = 0+(m+2)+1 from by ring,
      show 3*m+3+1 = (2*m+1)+(m+2)+1 from by ring,
      show 3+2*m = 2*m+3 from by ring]
  apply stepStar_stepPlus_stepPlus (r3r2r2_drain (d := 2*m+3) (m+2) 0 (2*m+1) f)
  rw [show 0+1 = 0+1 from rfl,
      show (2*m+1)+2*(m+2)+1 = (4*m+5)+1 from by ring,
      show f+2*(m+2) = f+2*m+4 from by ring]
  step fm; step fm; step fm
  ring_nf; finish

-- Chain + drain for odd case: from after R4+R5+R3+R1+R1 opening
theorem odd_body : ⟨0, 2*m+1, 2+1, 3, 4*m+6, f⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+4, 4*m+9, f+2*m+7⟩ := by
  rw [show (4*m+6 : ℕ) = (3*m+5)+m+1 from by ring,
      show (2*m+1 : ℕ) = 1+2*m from by ring]
  apply stepStar_stepPlus_stepPlus (r3r1r1_chain (b := 1) (f := f) m 2 3 (3*m+5))
  rw [show 2+m+1 = (m+2)+1 from by ring,
      show 3*m+5+1 = (3*m+5)+1 from rfl,
      show 3+2*m = 2*m+3 from by ring]
  step fm; step fm; step fm
  rw [show m+2+1 = 0+(m+2)+1 from by ring,
      show 3*m+6 = (2*m+3)+(m+2)+1 from by ring,
      show 2*m+3+1 = 2*m+4 from by ring]
  apply stepStar_trans (r3r2r2_drain (d := 2*m+4) (m+2) 0 (2*m+3) (f+1))
  rw [show 0+1 = 0+1 from rfl,
      show (2*m+3)+2*(m+2)+1 = (4*m+7)+1 from by ring,
      show f+1+2*(m+2) = f+2*m+5 from by ring]
  step fm; step fm; step fm
  ring_nf; finish

-- Opening: R4 + R5+R3+R1+R1 for even d
theorem even_opening :
    ⟨0, 0, 0, 2*m+2, 4*m+5, f+1⟩ [fm]⊢⁺ ⟨0, 2*m, 2+1, 3, 4*m+4, f⟩ := by
  rw [show (2*m+2 : ℕ) = 0 + (2*m+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (e := 4*m+5) (f := f+1) (2*m+2) 0)
  simp only [Nat.zero_add]
  rw [show (4*m+5 : ℕ) = (4*m+4) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (2*m+2 : ℕ) = (2*m+1) + 1 from by ring]
  step fm
  rw [show (2*m+1 : ℕ) = (2*m) + 1 from by ring]
  step fm
  finish

-- Opening: R4 + R5+R3+R1+R1 for odd d
theorem odd_opening :
    ⟨0, 0, 0, 2*m+3, 4*m+7, f+1⟩ [fm]⊢⁺ ⟨0, 2*m+1, 2+1, 3, 4*m+6, f⟩ := by
  rw [show (2*m+3 : ℕ) = 0 + (2*m+3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (e := 4*m+7) (f := f+1) (2*m+3) 0)
  simp only [Nat.zero_add]
  rw [show (4*m+7 : ℕ) = (4*m+6) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (2*m+3 : ℕ) = (2*m+2) + 1 from by ring]
  step fm
  rw [show (2*m+2 : ℕ) = (2*m+1) + 1 from by ring]
  step fm
  finish

-- Even transition
theorem even_trans : ⟨0, 0, 0, 2*m+2, 4*m+5, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+3, 4*m+7, f+2*m+6⟩ :=
  stepPlus_stepStar_stepPlus even_opening (stepPlus_stepStar even_body)

-- Odd transition
theorem odd_trans : ⟨0, 0, 0, 2*m+3, 4*m+7, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+4, 4*m+9, f+2*m+7⟩ :=
  stepPlus_stepStar_stepPlus odd_opening (stepPlus_stepStar odd_body)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 5, 8⟩) (by execute fm 19)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d f, q = ⟨0, 0, 0, d + 2, 2 * (d + 2) + 1, f + 1⟩)
  · intro c ⟨d, f, hq⟩; subst hq
    rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      refine ⟨⟨0, 0, 0, 2*K+3, 4*K+7, f+2*K+6⟩,
             ⟨2*K+1, f+2*K+5, by ring_nf⟩, ?_⟩
      rw [show 2 * (2 * K + 2) + 1 = 4 * K + 5 from by ring]
      exact even_trans
    · subst hK
      refine ⟨⟨0, 0, 0, 2*K+4, 4*K+9, f+2*K+7⟩,
             ⟨2*K+2, f+2*K+6, by ring_nf⟩, ?_⟩
      rw [show 2 * (2 * K + 1 + 2) + 1 = 4 * K + 7 from by ring]
      exact odd_trans
  · exact ⟨0, 7, by ring_nf⟩
