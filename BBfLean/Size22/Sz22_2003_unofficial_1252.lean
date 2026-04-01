import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1252: [5/6, 77/2, 52/35, 3/13, 75/11]

Vector representation:
```
-1 -1  1  0  0  0
-1  0  0  1  1  0
 2  0 -1 -1  0  1
 0  1  0  0  0 -1
 0  1  2  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1252

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c+2, d, e, f⟩
  | _ => none

theorem f_to_b : ∀ k b d e f,
    ⟨(0 : ℕ), b, 0, d, e, f + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r3r1_chain : ∀ k b c d e f,
    ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e, f⟩ [fm]⊢*
    ⟨0, b, c + k + 1, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) d e (f + 1))
    ring_nf; finish

theorem r3r2_chain : ∀ k d e f,
    ⟨(0 : ℕ), 0, k, d + 1, e, f⟩ [fm]⊢*
    ⟨0, 0, 0, d + k + 1, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · ring_nf; finish
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih (d + 1) (e + 2) (f + 1))
    ring_nf; finish

theorem main_trans_even (m : ℕ) :
    ⟨(0 : ℕ), 0, 0, 4 * m + 3, (6 * m + 5) * (m + 1), 6 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 5, (3 * m + 4) * (2 * m + 3), 6 * m + 6⟩ := by
  -- First R4 step for ⊢⁺
  rw [show 6 * m + 3 = (6 * m + 2) + 1 from by ring]
  step fm
  -- Remaining R4 drain
  show ⟨0, 1, 0, 4 * m + 3, (6 * m + 5) * (m + 1), 6 * m + 2⟩ [fm]⊢*
    ⟨0, 0, 0, 4 * m + 5, (3 * m + 4) * (2 * m + 3), 6 * m + 6⟩
  rw [show (6 * m + 2 : ℕ) = 0 + (6 * m + 2) from by ring]
  apply stepStar_trans (f_to_b (6 * m + 2) 1 (4 * m + 3) ((6 * m + 5) * (m + 1)) 0)
  rw [show 1 + (6 * m + 2) = 6 * m + 3 from by ring]
  -- R5 once
  rw [show (6 * m + 5) * (m + 1) = (6 * m + 5) * m + 6 * m + 4 + 1 from by ring]
  step fm
  -- R3+R1+R1 chain (3*m+2 rounds)
  rw [show 6 * m + 4 = 0 + 2 * (3 * m + 2) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show 4 * m + 3 = (m + 1) + (3 * m + 2) from by ring]
  apply stepStar_trans (r3r1_chain (3 * m + 2) 0 1 (m + 1)
    ((6 * m + 5) * m + 6 * m + 4) 0)
  rw [show 1 + (3 * m + 2) + 1 = 3 * m + 4 from by ring,
      show 0 + (3 * m + 2) = 3 * m + 2 from by ring]
  -- R3+R2+R2 chain (3*m+4 rounds)
  rw [show m + 1 = m + 0 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (3 * m + 4) (m + 0)
    ((6 * m + 5) * m + 6 * m + 4) (3 * m + 2))
  rw [show m + 0 + (3 * m + 4) + 1 = 4 * m + 5 from by ring,
      show (6 * m + 5) * m + 6 * m + 4 + 2 * (3 * m + 4) = (3 * m + 4) * (2 * m + 3) from by ring,
      show 3 * m + 2 + (3 * m + 4) = 6 * m + 6 from by ring]
  finish

theorem main_trans_odd (m : ℕ) :
    ⟨(0 : ℕ), 0, 0, 4 * m + 5, (3 * m + 4) * (2 * m + 3), 6 * m + 6⟩ [fm]⊢⁺
    ⟨0, 0, 0, 4 * m + 7, (6 * m + 11) * (m + 2), 6 * m + 9⟩ := by
  -- First R4 step for ⊢⁺
  rw [show 6 * m + 6 = (6 * m + 5) + 1 from by ring]
  step fm
  -- Remaining R4 drain
  show ⟨0, 1, 0, 4 * m + 5, (3 * m + 4) * (2 * m + 3), 6 * m + 5⟩ [fm]⊢*
    ⟨0, 0, 0, 4 * m + 7, (6 * m + 11) * (m + 2), 6 * m + 9⟩
  rw [show (6 * m + 5 : ℕ) = 0 + (6 * m + 5) from by ring]
  apply stepStar_trans (f_to_b (6 * m + 5) 1 (4 * m + 5) ((3 * m + 4) * (2 * m + 3)) 0)
  rw [show 1 + (6 * m + 5) = 6 * m + 6 from by ring]
  -- R5 once
  rw [show (3 * m + 4) * (2 * m + 3) = (3 * m + 4) * (2 * m + 2) + 3 * m + 3 + 1 from by ring]
  step fm
  -- R3+R1+R1 chain (3*m+3 rounds)
  rw [show 6 * m + 7 = 1 + 2 * (3 * m + 3) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring,
      show 4 * m + 5 = (m + 2) + (3 * m + 3) from by ring]
  apply stepStar_trans (r3r1_chain (3 * m + 3) 1 1 (m + 2)
    ((3 * m + 4) * (2 * m + 2) + 3 * m + 3) 0)
  rw [show 1 + (3 * m + 3) + 1 = 3 * m + 5 from by ring,
      show 0 + (3 * m + 3) = 3 * m + 3 from by ring]
  -- R3+R1+R2 (b=1 case)
  rw [show m + 2 = (m + 1) + 1 from by ring]
  step fm; step fm; step fm
  -- R3+R2+R2 chain (3*m+5 rounds)
  rw [show m + 2 = (m + 1) + 1 from by ring]
  apply stepStar_trans (r3r2_chain (3 * m + 5) (m + 1)
    ((3 * m + 4) * (2 * m + 2) + 3 * m + 3 + 1) (3 * m + 3 + 1))
  rw [show m + 1 + (3 * m + 5) + 1 = 4 * m + 7 from by ring,
      show 3 * m + 3 + 1 + (3 * m + 5) = 6 * m + 9 from by ring,
      show (3 * m + 4) * (2 * m + 2) + 3 * m + 3 + 1 + 2 * (3 * m + 5) =
        (6 * m + 11) * (m + 2) from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 5, 3⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m, q = ⟨0, 0, 0, 4 * m + 3, (6 * m + 5) * (m + 1), 6 * m + 3⟩ ∨
                        q = ⟨0, 0, 0, 4 * m + 5, (3 * m + 4) * (2 * m + 3), 6 * m + 6⟩)
  · intro c ⟨m, hq⟩
    rcases hq with rfl | rfl
    · exact ⟨_, ⟨m, Or.inr rfl⟩, main_trans_even m⟩
    · exact ⟨_, ⟨m + 1, Or.inl (by ring_nf)⟩, main_trans_odd m⟩
  · exact ⟨0, Or.inl (by ring_nf)⟩

end Sz22_2003_unofficial_1252
