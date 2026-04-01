import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1576: [7/45, 4/3, 15/14, 11/2, 63/11]

Vector representation:
```
 0 -2 -1  1  0
 2 -1  0  0  0
-1  1  1 -1  0
-1  0  0  0  1
 0  2  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1576

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R5+R1 chain: drains c and e in lockstep, building d.
theorem r5r1_chain : ∀ k c d e, ⟨0, 0, c + k, d, e + k⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih c (d + 2) e); ring_nf; finish

-- R3+R2 chain: transfers d to a and c.
theorem r3r2_chain : ∀ k a c d e, ⟨a + 1, 0, c, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (c + 1) d e); ring_nf; finish

-- R4 drain: (k, 0, c, 0, e) -> (0, 0, c, 0, e+k).
theorem r4_drain : ∀ k c e, ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · step fm
    apply stepStar_trans (ih c (e + 1)); ring_nf; finish

-- Main transition: (0, 0, c+1, 0, c+F+2) ⊢⁺ (0, 0, 2c+3, 0, 2c+F+7)
theorem main_trans (c F : ℕ) :
    ⟨0, 0, c + 1, 0, c + F + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 3, 0, 2 * c + F + 7⟩ := by
  -- First R5+R1 step (manually, to get ⊢⁺)
  rw [show c + F + 2 = (c + F + 1) + 1 from by ring,
      show c + 1 = c + 1 from rfl]
  step fm; step fm
  -- Now at (0, 0, c, 2, c+F+1). Apply R5+R1 chain for c more rounds.
  have h := r5r1_chain c 0 2 (F + 1)
  rw [show 0 + c = c from by ring, show (F + 1) + c = c + F + 1 from by ring] at h
  apply stepStar_trans h
  rw [show 2 + 2 * c = 2 * c + 2 from by ring]
  -- Now at (0, 0, 0, 2c+2, F+1). R5+R2+R2.
  rw [show (F + 1 : ℕ) = F + 1 from rfl]
  step fm; step fm; step fm
  rw [show 2 * c + 2 + 1 = 2 * c + 3 from by ring]
  -- Now at (4, 0, 0, 2c+3, F). R3+R2 chain, 2c+3 rounds.
  rw [show (4 : ℕ) = 3 + 1 from rfl,
      show 2 * c + 3 = 0 + (2 * c + 3) from by ring]
  apply stepStar_trans (r3r2_chain (2 * c + 3) 3 0 0 F)
  rw [show 3 + (2 * c + 3) + 1 = 2 * c + 7 from by ring,
      show 0 + (2 * c + 3) = 2 * c + 3 from by ring]
  -- Now at (2c+7, 0, 2c+3, 0, F). R4 drain.
  apply stepStar_trans (r4_drain (2 * c + 7) (2 * c + 3) F)
  rw [show F + (2 * c + 7) = 2 * c + F + 7 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 5⟩) (by execute fm 11)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, F⟩ ↦ ⟨0, 0, c + 1, 0, c + F + 2⟩) ⟨0, 3⟩
  intro ⟨c, F⟩
  exact ⟨⟨2 * c + 2, F + 3⟩, by
    show ⟨0, 0, c + 1, 0, c + F + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 2 + 1, 0, (2 * c + 2) + (F + 3) + 2⟩
    rw [show 2 * c + 2 + 1 = 2 * c + 3 from by ring,
        show (2 * c + 2) + (F + 3) + 2 = 2 * c + F + 7 from by ring]
    exact main_trans c F⟩

end Sz22_2003_unofficial_1576
