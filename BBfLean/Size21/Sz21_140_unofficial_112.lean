import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #112: [77/15, 2/3, 9/14, 5/11, 45/2]

Vector representation:
```
 0 -1 -1  1  1
 1 -1  0  0  0
-1  2  0 -1  0
 0  0  1  0 -1
-1  2  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_112

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | _ => none

-- R4 repeated: e → c
theorem e_to_c : ∀ k, ∀ a c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show c + (k + 1) = (c + 1) + k from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1))
  ring_nf; finish

-- R3,R2,R2 drain: d → a
theorem r3r2r2_drain : ∀ k, ∀ a e, ⟨a + 1, 0, 0, k, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + 1 + (k + 1) = (a + 1) + 1 + k from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (a + 1) e)
  ring_nf; finish

-- R1x2,R3 rounds: a,c → d,e
theorem r1r1r3_rounds : ∀ k, ∀ A C D E, ⟨A + k, 2, C + 2 * k, D, E⟩ [fm]⊢* ⟨A, 2, C, D + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · exists 0
  have h1 : fm ⟨A + k + 1, 2, C + 2 * k + 2, D, E⟩ =
             some ⟨A + k + 1, 1, C + 2 * k + 1, D + 1, E + 1⟩ := by
    show fm ⟨A + k + 1, 1 + 1, (C + 2 * k + 1) + 1, D, E⟩ =
         some ⟨A + k + 1, 1, C + 2 * k + 1, D + 1, E + 1⟩
    simp [fm]
  have h2 : fm ⟨A + k + 1, 1, C + 2 * k + 1, D + 1, E + 1⟩ =
             some ⟨A + k + 1, 0, C + 2 * k, D + 2, E + 2⟩ := by
    show fm ⟨A + k + 1, 0 + 1, (C + 2 * k) + 1, D + 1, E + 1⟩ =
         some ⟨A + k + 1, 0, C + 2 * k, D + 2, E + 2⟩
    simp [fm]
  have h3 : fm ⟨A + k + 1, 0, C + 2 * k, D + 2, E + 2⟩ =
             some ⟨A + k, 2, C + 2 * k, D + 1, E + 2⟩ := by
    show fm ⟨(A + k) + 1, 0, C + 2 * k, (D + 1) + 1, E + 2⟩ =
         some ⟨A + k, (0 + 2), C + 2 * k, D + 1, E + 2⟩
    simp [fm]
  rw [show A + (k + 1) = A + k + 1 from by ring,
      show C + 2 * (k + 1) = C + 2 * k + 2 from by ring]
  apply stepStar_trans (step_stepStar h1)
  apply stepStar_trans (step_stepStar h2)
  apply stepStar_trans (step_stepStar h3)
  apply stepStar_trans (ih A C (D + 1) (E + 2))
  ring_nf; finish

-- Even case
theorem even_trans : ⟨2 * m, 2, 2 * m + 1, 0, 0⟩ [fm]⊢* ⟨2 * m + 2, 0, 0, 0, 2 * m + 1⟩ := by
  apply stepStar_trans (c₂ := ⟨m, 2, 1, m, 2 * m⟩)
  · have h := r1r1r3_rounds m m 1 0 0
    rw [show 1 + 2 * m = 2 * m + 1 from by ring] at h
    simp only [Nat.zero_add] at h
    rw [show m + m = 2 * m from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨m + 1, 0, 0, m + 1, 2 * m + 1⟩)
  · step fm; step fm; finish
  have h := r3r2r2_drain (m + 1) m (2 * m + 1)
  rw [show m + 1 + (m + 1) = 2 * m + 2 from by ring] at h
  exact h

-- Odd case
theorem odd_trans : ⟨2 * m + 1, 2, 2 * m + 2, 0, 0⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 0, 2 * m + 2⟩ := by
  apply stepStar_trans (c₂ := ⟨m + 1, 2, 2, m, 2 * m⟩)
  · have h := r1r1r3_rounds m (m + 1) 2 0 0
    rw [show 2 + 2 * m = 2 * m + 2 from by ring,
        show m + 1 + m = 2 * m + 1 from by ring] at h
    simp only [Nat.zero_add] at h
    exact h
  apply stepStar_trans (c₂ := ⟨m + 1, 0, 0, m + 2, 2 * m + 2⟩)
  · step fm; step fm; finish
  have h := r3r2r2_drain (m + 2) m (2 * m + 2)
  rw [show m + 1 + (m + 2) = 2 * m + 3 from by ring] at h
  exact h

-- Main transition: (n+1, 0, 0, 0, n) → (n+2, 0, 0, 0, n+1)
theorem main_trans : ⟨n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, n + 1⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + 1, 0, n, 0, 0⟩)
  · have h := e_to_c n (n + 1) 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨n, 2, n + 1, 0, 0⟩)
  · show fm ⟨n + 1, 0, n, 0, 0⟩ = some ⟨n, 2, n + 1, 0, 0⟩; simp [fm]
  -- Parity split
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact even_trans
  · subst hm
    exact odd_trans

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n + 1, 0, 0, 0, n⟩) 0
  intro n; exact ⟨n + 1, main_trans⟩
