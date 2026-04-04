import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1855: [9/35, 2/5, 275/6, 7/11, 165/2]

Vector representation:
```
 0  2 -1 -1  0
 1  0 -1  0  0
-1 -1  2  0  1
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1855

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

-- R4 chain: move e to d
theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

-- R3/R1/R1 chain: drain d by 2 per round
theorem r3r1r1_chain : ∀ k, ∀ b d e,
    ⟨a + k, b + 1, 0, d + 2 * k, e⟩ [fm]⊢* ⟨a, b + 1 + 3 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    step fm
    step fm
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (b := b + 3) d (e + 1))
    ring_nf; finish

-- R3/R2/R2 chain: drain b
theorem r3r2r2_chain : ∀ k, ∀ a e,
    ⟨a + 1, k, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    step fm
    step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

-- Tail when D=1: R3/R1/R2
theorem tail_d1 : ⟨a + 1, b + 1, 0, 1, e⟩ [fm]⊢* ⟨a + 1, b + 2, 0, 0, e + 1⟩ := by
  step fm
  step fm
  step fm
  finish

-- Combined phases after R5+R1: (a+1+m, 3, 0, 2m+1, 1) ⊢* (a+3m+5, 0, 0, 4m+6, 0)
theorem combined_phases :
    ⟨a + 1 + m, 3, 0, 2 * m + 1, 1⟩ [fm]⊢* ⟨a + 3 * m + 5, 0, 0, 4 * m + 6, 0⟩ := by
  -- R3/R1/R1 chain: m rounds
  rw [show a + 1 + m = (a + 1) + m from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r3r1r1_chain m (a := a + 1) (b := 2) (d := 1) (e := 1))
  -- After chain: (a+1, 2+1+3*m, 0, 1, 1+m)
  rw [show 2 + 1 + 3 * m = (3 * m + 2) + 1 from by ring]
  -- Tail D=1
  apply stepStar_trans (tail_d1 (a := a) (b := 3 * m + 2) (e := 1 + m))
  -- After tail: (a+1, 3*m+4, 0, 0, m+2)
  rw [show 3 * m + 2 + 2 = 3 * m + 4 from by ring,
      show 1 + m + 1 = m + 2 from by ring,
      show a + 1 = (a + 0) + 1 from by ring]
  -- R3/R2/R2 chain
  apply stepStar_trans (r3r2r2_chain (3 * m + 4) (a := a + 0) (e := m + 2))
  -- After chain: (a+3m+5, 0, 0, 0, 4m+6)
  rw [show a + 0 + (3 * m + 4) + 1 = a + 3 * m + 5 from by ring,
      show m + 2 + (3 * m + 4) = 4 * m + 6 from by ring]
  -- R4 chain
  rw [show 4 * m + 6 = 0 + (4 * m + 6) from by ring]
  exact e_to_d (4 * m + 6) (a := a + 3 * m + 5) (d := 0) (e := 0)

-- Main transition: (a+m+2, 0, 0, 2m+2, 0) ⊢⁺ (a+3m+5, 0, 0, 4m+6, 0)
theorem main_trans :
    ⟨a + m + 2, 0, 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨a + 3 * m + 5, 0, 0, 4 * m + 6, 0⟩ := by
  -- R5
  rw [show a + m + 2 = (a + m + 1) + 1 from by ring]
  step fm
  -- R1
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  -- Remaining phases
  rw [show a + m + 1 = a + 1 + m from by ring]
  exact combined_phases

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, m⟩ ↦ ⟨a + m + 2, 0, 0, 2 * m + 2, 0⟩) ⟨0, 0⟩
  intro ⟨a, m⟩; exact ⟨⟨a + m + 1, 2 * m + 2⟩, by
    show ⟨a + m + 2, 0, 0, 2 * m + 2, 0⟩ [fm]⊢⁺
      ⟨(a + m + 1) + (2 * m + 2) + 2, 0, 0, 2 * (2 * m + 2) + 2, 0⟩
    rw [show (a + m + 1) + (2 * m + 2) + 2 = a + 3 * m + 5 from by ring,
        show 2 * (2 * m + 2) + 2 = 4 * m + 6 from by ring]
    exact main_trans⟩

end Sz22_2003_unofficial_1855
