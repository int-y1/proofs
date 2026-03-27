import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #140: [1/45, 2/35, 7865/2, 21/11, 5/39]

Vector representation:
```
 0 -2 -1  0  0  0
 1  0 -1 -1  0  0
-1  0  1  0  2  1
 0  1  0  1 -1  0
 0 -1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_140

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+2, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R4 chain: e → b,d
theorem e_to_bd : ∀ k b d e f, ⟨0, b, 0, d, e+k, f⟩ [fm]⊢* ⟨(0 : ℕ), b+k, 0, d+k, e, f⟩ := by
  intro k; induction k with
  | zero => intro b d e f; exists 0
  | succ k ih =>
    intro b d e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _)
    ring_nf; finish

-- drain: R5+R1 chain, then final R5
-- (0, 3k+2, 0, D, 0, f+k+1) →* (0, 1, 1, D, 0, f)
theorem drain : ∀ k D f, ⟨0, 3*k+2, 0, D, 0, f+k+1⟩ [fm]⊢* ⟨(0 : ℕ), 1, 1, D, 0, f⟩ := by
  intro k; induction k with
  | zero =>
    intro D f
    -- (0, 2, 0, D, 0, f+1) → R5 → (0, 1, 1, D, 0, f)
    rw [show 3 * 0 + 2 = (0 : ℕ) + 1 + 1 from by ring,
        show f + 0 + 1 = f + 1 from by ring,
        show (0 : ℕ) = 0 from rfl]
    step fm; finish
  | succ k ih =>
    intro D f
    -- (0, 3(k+1)+2, 0, D, 0, f+(k+1)+1) = (0, 3k+5, 0, D, 0, f+k+2)
    -- R5: (0, 3k+4, 1, D, 0, f+k+1)
    -- R1: (0, 3k+2, 0, D, 0, f+k+1)
    -- IH
    rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 1 + 1 + 1 from by ring,
        show f + (k + 1) + 1 = (f + k + 1) + 1 from by ring]
    step fm
    rw [show 3 * k + 2 + 1 + 1 = (3 * k + 2) + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih D f)
    finish

-- bounce: R2+R3 chain
-- (0, 1, 1, k, e, f) →* (0, 1, 1, 0, e+2*k, f+k)
theorem bounce : ∀ k e f, ⟨0, 1, 1, k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 1, 1, 0, e+2*k, f+k⟩ := by
  intro k; induction k with
  | zero => intro e f; exists 0
  | succ k ih =>
    intro e f
    rw [show (k + 1) = k + 1 from rfl]
    -- R2: (0, 1, 1, k+1, e, f) → (1, 1, 0, k, e, f)
    step fm
    -- R3: (1, 1, 0, k, e, f) → (0, 1, 1, k, e+2, f+1)
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- main transition: (0, 0, 0, 1, 3G+2, F+G+1) ⊢⁺ (0, 0, 0, 1, 6G+5, F+3G+3)
theorem main_trans (G F : ℕ) : ⟨0, 0, 0, 1, 3*G+2, F+G+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 6*G+5, F+3*G+3⟩ := by
  -- Phase 1: e_to_bd (3G+2 steps of R4)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*G+2, 0, 3*G+3, 0, F+G+1⟩)
  · have h := e_to_bd (3*G+2) 0 1 0 (F+G+1)
    simp only [Nat.zero_add] at h
    rw [show 1 + (3 * G + 2) = 3 * G + 3 from by ring] at h
    exact h
  -- Phase 2: drain (k=G)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 1, 3*G+3, 0, F⟩)
  · exact drain G (3*G+3) F
  -- Phase 3: bounce (k=3G+3)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 1, 1, 0, 6*G+6, F+3*G+3⟩)
  · have h := bounce (3*G+3) 0 F
    simp only [Nat.zero_add] at h
    rw [show 2 * (3 * G + 3) = 6 * G + 6 from by ring,
        show F + (3 * G + 3) = F + 3 * G + 3 from by ring] at h
    exact h
  -- Phase 4: wrap-up (R4, R1)
  rw [show (6 * G + 6) = (6 * G + 5) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨G, F⟩ ↦ ⟨0, 0, 0, 1, 3*G+2, F+G+1⟩) ⟨0, 1⟩
  intro ⟨G, F⟩
  refine ⟨⟨2*G+1, F+G+1⟩, ?_⟩
  show ⟨0, 0, 0, 1, 3*G+2, F+G+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, 3*(2*G+1)+2, (F+G+1)+(2*G+1)+1⟩
  rw [show 3 * (2 * G + 1) + 2 = 6 * G + 5 from by ring,
      show (F + G + 1) + (2 * G + 1) + 1 = F + 3 * G + 3 from by ring]
  exact main_trans G F

end Sz22_2003_unofficial_140
