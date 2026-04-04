import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1864: [9/35, 242/5, 5/33, 7/11, 75/2]

Vector representation:
```
 0  2 -1 -1  0
 1  0 -1  0  2
 0 -1  1  0 -1
 0  0  0  1 -1
-1  1  2  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1864

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+2, d, e⟩
  | _ => none

-- R4 loop: transfer e to d.
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _); ring_nf; finish

-- Drain: one round.
theorem drain_one : ⟨a + 1, b, 0, d + 2, 0⟩ [fm]⊢* ⟨a, b + 5, 0, d, 0⟩ := by
  step fm; step fm; step fm; finish

-- Drain iterated k rounds.
theorem drain : ∀ k, ∀ a b d, ⟨a + k, b, 0, d + 2 * k, 0⟩ [fm]⊢* ⟨a, b + 5 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (a + 1) b (d + 2))
    apply stepStar_trans drain_one
    ring_nf; finish

-- R3+R2 loop: each round b-=1, a+=1, e+=1.
theorem r3r2_loop : ∀ k, ∀ a b e, ⟨a, b + k, 0, 0, e + 1⟩ [fm]⊢* ⟨a + k, b, 0, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih a (b + 1) e)
    rw [show e + k + 1 = (e + k) + 1 from by ring]
    step fm
    step fm
    ring_nf; finish

-- Even endgame: (a+1, 5*m, 0, 0, 0) →⁺ (a+5*m+3, 0, 0, 0, 5*m+5)
theorem even_end : ⟨a + 1, 5 * m, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 5 * m + 3, 0, 0, 0, 5 * m + 5⟩ := by
  step fm
  step fm
  step fm
  show ⟨a + 1 + 1, 5 * m + 1, 0, 0, 4⟩ [fm]⊢* ⟨a + 5 * m + 3, 0, 0, 0, 5 * m + 5⟩
  rw [show a + 1 + 1 = a + 2 from by ring,
      show 5 * m + 1 = 0 + (5 * m + 1) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3r2_loop (5 * m + 1) (a + 2) 0 3)
  ring_nf; finish

-- Odd endgame: (a+1, 5*m, 0, 1, 0) →⁺ (a+5*m+4, 0, 0, 0, 5*m+5)
theorem odd_end : ⟨a + 1, 5 * m, 0, 1, 0⟩ [fm]⊢⁺ ⟨a + 5 * m + 4, 0, 0, 0, 5 * m + 5⟩ := by
  step fm
  step fm
  step fm
  show ⟨a + 1, 5 * m + 1 + 2, 0, 0, 2⟩ [fm]⊢* ⟨a + 5 * m + 4, 0, 0, 0, 5 * m + 5⟩
  rw [show 5 * m + 1 + 2 = 0 + (5 * m + 3) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_loop (5 * m + 3) (a + 1) 0 1)
  ring_nf; finish

-- Even full transition: (a+m+1, 0, 0, 0, 2*m) →⁺ (a+5*m+3, 0, 0, 0, 5*m+5)
theorem even_trans (m : ℕ) : ⟨a + m + 1, 0, 0, 0, 2 * m⟩ [fm]⊢⁺ ⟨a + 5 * m + 3, 0, 0, 0, 5 * m + 5⟩ := by
  rw [show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact e_to_d (2 * m) (a := a + m + 1) (d := 0) (e := 0)
  rw [show a + m + 1 = (a + 1) + m from by ring,
      show 0 + 2 * m = 0 + 2 * m from rfl]
  apply stepStar_stepPlus_stepPlus
  · exact drain m (a + 1) 0 0
  rw [show 0 + 5 * m = 5 * m from by ring]
  exact even_end

-- Odd full transition: (a+m+1, 0, 0, 0, 2*m+1) →⁺ (a+5*m+4, 0, 0, 0, 5*m+5)
theorem odd_trans (m : ℕ) : ⟨a + m + 1, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨a + 5 * m + 4, 0, 0, 0, 5 * m + 5⟩ := by
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact e_to_d (2 * m + 1) (a := a + m + 1) (d := 0) (e := 0)
  rw [show a + m + 1 = (a + 1) + m from by ring,
      show 0 + (2 * m + 1) = 1 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact drain m (a + 1) 0 1
  rw [show 0 + 5 * m = 5 * m from by ring]
  exact odd_end

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩)
  · execute fm 5
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 1 ∧ 2 * a ≥ e + 1)
  · intro c ⟨A, E, hq, hE, hA⟩; subst hq
    rcases Nat.even_or_odd E with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- e even: E = 2*m, m >= 1
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨F, rfl⟩ : ∃ F, A = F + m + 1 := ⟨A - m - 1, by omega⟩
      refine ⟨⟨F + 5 * m + 3, 0, 0, 0, 5 * m + 5⟩,
        ⟨F + 5 * m + 3, 5 * m + 5, rfl, by omega, by omega⟩, ?_⟩
      exact even_trans m
    · -- e odd: E = 2*m + 1, m >= 0
      subst hm
      obtain ⟨F, rfl⟩ : ∃ F, A = F + m + 1 := ⟨A - m - 1, by omega⟩
      refine ⟨⟨F + 5 * m + 4, 0, 0, 0, 5 * m + 5⟩,
        ⟨F + 5 * m + 4, 5 * m + 5, rfl, by omega, by omega⟩, ?_⟩
      exact odd_trans m
  · exact ⟨3, 5, rfl, by omega, by omega⟩
