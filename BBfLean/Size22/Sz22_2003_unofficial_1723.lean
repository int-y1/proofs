import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1723: [8/15, 3/14, 55/2, 49/5, 10/11]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  1
 0  0 -1  2  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1723

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih a (c + 1) (e + 1))
  rw [show c + 1 + k = c + (k + 1) from by ring,
      show e + 1 + k = e + (k + 1) from by ring]; finish

theorem r4_chain : ∀ k, ∀ d e, ⟨0, 0, k, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]; step fm
  apply stepStar_trans (ih (d + 2) e)
  rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]; finish

theorem r2_chain : ∀ k, ∀ A B D E, ⟨A + k, B, 0, D + k, E⟩ [fm]⊢* ⟨A, B + k, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro A B D E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show D + (k + 1) = (D + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih A (B + 1) D E)
  rw [show B + 1 + k = B + (k + 1) from by ring]; finish

theorem d_drain_round_0 : ∀ D E, ⟨0, 0, 0, D + 4, E + 1⟩ [fm]⊢* ⟨0, 3, 0, D, E⟩ := by
  intro D E
  rw [show E + 1 = E + 1 from rfl]
  step fm
  -- state: (1, 0, 1, D+4, E)
  rw [show D + 4 = (D + 3) + 1 from by ring]
  step fm
  -- state: (0, 1, 1, D+3, E)
  step fm
  -- state: (3, 0, 0, D+3, E)
  rw [show D + 3 = (D + 2) + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  -- state: (2, 1, 0, D+2, E)
  rw [show D + 2 = (D + 1) + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  -- state: (1, 2, 0, D+1, E)
  rw [show D + 1 = D + 1 from rfl]
  step fm
  -- state: (0, 3, 0, D, E)
  finish

theorem d_drain_round_pos : ∀ B D E,
    ⟨0, B + 1, 0, D + 4, E + 1⟩ [fm]⊢* ⟨0, B + 4, 0, D, E⟩ := by
  intro B D E
  rw [show E + 1 = E + 1 from rfl]
  step fm
  -- state: (1, B+1, 1, D+4, E)
  rw [show B + 1 = B + 1 from rfl]
  step fm
  -- state: (4, B, 0, D+4, E)
  rw [show (4 : ℕ) = 3 + 1 from by ring, show D + 4 = (D + 3) + 1 from by ring]
  step fm
  -- state: (3, B+1, 0, D+3, E)
  rw [show (3 : ℕ) = 2 + 1 from by ring, show D + 3 = (D + 2) + 1 from by ring]
  step fm
  -- state: (2, B+2, 0, D+2, E)
  rw [show (2 : ℕ) = 1 + 1 from by ring, show D + 2 = (D + 1) + 1 from by ring]
  step fm
  -- state: (1, B+3, 0, D+1, E)
  rw [show D + 1 = D + 1 from rfl]
  step fm
  -- state: (0, B+4, 0, D, E)
  finish

theorem d_drain_loop : ∀ k, ∀ B D E,
    ⟨0, B + 1, 0, D + 4 * k, E + k⟩ [fm]⊢* ⟨0, B + 3 * k + 1, 0, D, E⟩ := by
  intro k; induction' k with k ih <;> intro B D E
  · simp; exists 0
  rw [show D + 4 * (k + 1) = (D + 4 * k) + 4 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  apply stepStar_trans (d_drain_round_pos B (D + 4 * k) (E + k))
  rw [show B + 4 = (B + 3) + 1 from by ring]
  apply stepStar_trans (ih (B + 3) D E)
  rw [show B + 3 + 3 * k + 1 = B + 3 * (k + 1) + 1 from by ring]; finish

theorem r3r1_chain : ∀ k, ∀ a e,
    ⟨a + 2, k + 1, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k + 4, 0, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; finish
  rw [show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring,
      show a + 2 = (a + 2) from rfl]
  step fm
  -- state: (a+1, k+2, 1, 0, e+1)
  rw [show (k : ℕ) + 1 + 1 = (k + 1) + 1 from by ring]
  step fm
  -- state: (a+4, k+1, 0, 0, e+1)
  rw [show a + 4 = (a + 2) + 2 from by ring]
  apply stepStar_trans (ih (a + 2) (e + 1))
  rw [show a + 2 + 2 * k + 4 = a + 2 * (k + 1) + 4 from by ring,
      show e + 1 + k + 1 = e + (k + 1) + 1 from by ring]; finish

theorem main_trans (A E : ℕ) :
    ⟨2 * A + 4, 0, 0, 0, E + 1⟩ [fm]⊢⁺ ⟨2 * (3 * A + 5) + 4, 0, 0, 0, (E + 4 * A + 6) + 1⟩ := by
  have p1 : ⟨2 * A + 4, 0, 0, 0, E + 1⟩ [fm]⊢*
      ⟨0, 0, 2 * A + 4, 0, E + 2 * A + 5⟩ := by
    have h := r3_chain (2 * A + 4) 0 0 (E + 1)
    simp at h
    rw [show E + 1 + (2 * A + 4) = E + 2 * A + 5 from by ring] at h
    exact h
  have p2 : ⟨0, 0, 2 * A + 4, 0, E + 2 * A + 5⟩ [fm]⊢*
      ⟨0, 0, 0, 4 * A + 8, E + 2 * A + 5⟩ := by
    have h := r4_chain (2 * A + 4) 0 (E + 2 * A + 5)
    rw [show 0 + 2 * (2 * A + 4) = 4 * A + 8 from by ring] at h
    exact h
  have p3 : ⟨0, 0, 0, 4 * A + 8, E + 2 * A + 5⟩ [fm]⊢*
      ⟨0, 3, 0, 4 * A + 4, E + 2 * A + 4⟩ := by
    rw [show 4 * A + 8 = (4 * A + 4) + 4 from by ring,
        show E + 2 * A + 5 = (E + 2 * A + 4) + 1 from by ring]
    exact d_drain_round_0 (4 * A + 4) (E + 2 * A + 4)
  have p4 : ⟨0, 3, 0, 4 * A + 4, E + 2 * A + 4⟩ [fm]⊢*
      ⟨0, 3 * A + 6, 0, 0, E + A + 3⟩ := by
    rw [show (3 : ℕ) = 2 + 1 from by ring,
        show 4 * A + 4 = 0 + 4 * (A + 1) from by ring,
        show E + 2 * A + 4 = (E + A + 3) + (A + 1) from by ring]
    have h := d_drain_loop (A + 1) 2 0 (E + A + 3)
    rw [show 2 + 3 * (A + 1) + 1 = 3 * A + 6 from by ring] at h
    exact h
  have p5 : ⟨0, 3 * A + 6, 0, 0, E + A + 3⟩ [fm]⊢⁺
      ⟨4, 3 * A + 5, 0, 0, E + A + 2⟩ := by
    rw [show 3 * A + 6 = (3 * A + 5) + 1 from by ring,
        show E + A + 3 = (E + A + 2) + 1 from by ring]
    step fm; step fm; finish
  have p6 : ⟨4, 3 * A + 5, 0, 0, E + A + 2⟩ [fm]⊢*
      ⟨6 * A + 14, 0, 0, 0, E + 4 * A + 7⟩ := by
    rw [show (4 : ℕ) = 2 + 2 from by ring,
        show 3 * A + 5 = (3 * A + 4) + 1 from by ring]
    have h := r3r1_chain (3 * A + 4) 2 (E + A + 2)
    rw [show 2 + 2 * (3 * A + 4) + 4 = 6 * A + 14 from by ring,
        show E + A + 2 + (3 * A + 4) + 1 = E + 4 * A + 7 from by ring] at h
    exact h
  rw [show 2 * (3 * A + 5) + 4 = 6 * A + 14 from by ring,
      show (E + 4 * A + 6) + 1 = E + 4 * A + 7 from by ring]
  exact stepPlus_stepStar_stepPlus
    (stepStar_stepPlus_stepPlus
      (stepStar_trans p1 (stepStar_trans p2 (stepStar_trans p3 p4))) p5) p6

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 1⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨A, E⟩ ↦ ⟨2 * A + 4, 0, 0, 0, E + 1⟩) ⟨0, 0⟩
  intro ⟨A, E⟩
  refine ⟨⟨3 * A + 5, E + 4 * A + 6⟩, ?_⟩
  exact main_trans A E

end Sz22_2003_unofficial_1723
