import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1973: [99/35, 25/22, 4/5, 7/3, 15/2]

Vector representation:
```
 0  2 -1 -1  1
-1  0  2  0 -1
 2  0 -1  0  0
 0 -1  0  1  0
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1973

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R3 chain: convert c to a when d=0, e=0.
theorem r3_chain : ∀ k, ∀ a b, ⟨a, b, k, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, b, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) b)
    ring_nf; finish

-- R4 chain: convert b to d when c=0, e=0.
theorem r4_chain : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- R2 drain: when d=0, drain a and e into c.
theorem r2_drain : ∀ k, ∀ a b c, ⟨a + k, b, c, 0, k⟩ [fm]⊢* ⟨a, b, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b (c + 2))
    ring_nf; finish

-- One spiral round: R1 fires twice, then R2 fires once.
theorem spiral_round : ∀ k, ∀ a b d e, ⟨a + k, b, 2, d + 2 * k, e⟩ [fm]⊢* ⟨a, b + 4 * k, 2, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a (b + 4) d (e + 1))
    ring_nf; finish

-- Main transition: C(m) = (2m+2, 0, 0, 2m+1, 0) ->+ C(2m+1) = (4m+4, 0, 0, 4m+3, 0).
theorem main_trans : ⟨2 * m + 2, 0, 0, 2 * m + 1, 0⟩ [fm]⊢⁺ ⟨4 * m + 4, 0, 0, 4 * m + 3, 0⟩ := by
  -- Opening: R5, R1, R2 -> (2m, 3, 2, 2m, 0)
  step fm; step fm; step fm
  -- Spiral: m rounds. (m+m, 3, 2, m+m, 0) -> (m, 3+4*m, 2, 0, 0+m)
  have h1 := spiral_round m m 3 0 0
  rw [show 0 + 2 * m = m + m from by ring,
      show m + m = 2 * m from by ring] at h1
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  -- R2 drain: m steps. (m, 3+4m, 2, 0, m) -> (0, 3+4m, 2+2m, 0, 0)
  have h2 := r2_drain (0 + m) 0 (3 + 4 * m) 2
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  -- R3 chain: (0, 3+4m, 2+2m, 0, 0) -> (4m+4, 3+4m, 0, 0, 0)
  rw [show 2 + 2 * m = 2 * m + 2 from by ring,
      show 3 + 4 * m = 4 * m + 3 from by ring]
  apply stepStar_trans (r3_chain (2 * m + 2) 0 (4 * m + 3))
  rw [show 0 + 2 * (2 * m + 2) = 4 * m + 4 from by ring]
  -- R4 chain: (4m+4, 4m+3, 0, 0, 0) -> (4m+4, 0, 0, 4m+3, 0)
  apply stepStar_trans (r4_chain (4 * m + 3) (4 * m + 4) 0)
  rw [show 0 + (4 * m + 3) = 4 * m + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨2 * m + 2, 0, 0, 2 * m + 1, 0⟩) 0
  intro m; refine ⟨2 * m + 1, ?_⟩
  show ⟨2 * m + 2, 0, 0, 2 * m + 1, 0⟩ [fm]⊢⁺ ⟨2 * (2 * m + 1) + 2, 0, 0, 2 * (2 * m + 1) + 1, 0⟩
  rw [show 2 * (2 * m + 1) + 2 = 4 * m + 4 from by ring,
      show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring]
  exact main_trans
