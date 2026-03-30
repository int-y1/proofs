import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #857: [36/35, 5/33, 7/3, 11/7, 45/2]

Vector representation:
```
 2  2 -1 -1  0
 0 -1  1  0 -1
 0 -1  0  1  0
 0  0  0 -1  1
-1  2  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_857

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d, e⟩
  | _ => none

-- R5+R2+R2 drain: each round a -= 1, c += 3, e -= 2
theorem r5r2r2_drain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a (c + 3) e)
    ring_nf; finish

-- R3+R1 chain: each round a += 2, b += 1, c -= 1
theorem r3r1_chain : ∀ k, ∀ a b c, ⟨a, b + 1, c + k, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, b + 1 + k, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) (b + 1) c)
    ring_nf; finish

-- b_to_d drain: R3 repeated
theorem b_to_d : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- d_to_e drain: R4 repeated
theorem d_to_e : ∀ k, ∀ a e, ⟨a, 0, 0, k, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- Odd 4-step transition: (a+1, 0, c, 0, 1) ->+ (a+2, 2, c+1, 0, 0)
theorem odd_4step : ∀ a c, ⟨a + 1, 0, c, 0, 1⟩ [fm]⊢⁺ ⟨a + 2, 2, c + 1, 0, 0⟩ := by
  intro a c
  step fm; step fm; step fm; step fm; finish

-- Even transition: (a+k+1, 0, 0, 0, 2*k) ->+ (a+6*k+2, 0, 0, 0, 3*k+3)
theorem even_trans (k a : ℕ) : ⟨a + k + 1, 0, 0, 0, 2 * k⟩ [fm]⊢⁺ ⟨a + 6 * k + 2, 0, 0, 0, 3 * k + 3⟩ := by
  -- Drain k rounds: -> (a+1, 0, 3*k, 0, 0)
  have h1 : ⟨a + k + 1, 0, 0, 0, 2 * k⟩ [fm]⊢* ⟨a + 1, 0, 3 * k, 0, 0⟩ := by
    rw [show a + k + 1 = (a + 1) + k from by ring,
        show 2 * k = 0 + 2 * k from by ring,
        show 3 * k = 0 + 3 * k from by ring]
    exact r5r2r2_drain k (a + 1) 0 0
  -- R5: (a+1, 0, 3*k, 0, 0) -> (a, 2, 3*k+1, 0, 0)
  have h2 : ⟨a + 1, 0, 3 * k, 0, 0⟩ [fm]⊢ ⟨a, 2, 3 * k + 1, 0, 0⟩ := by simp [fm]
  -- R3+R1 chain (3*k+1) rounds: -> (a+6*k+2, 3*k+3, 0, 0, 0)
  have h3 : ⟨a, 2, 3 * k + 1, 0, 0⟩ [fm]⊢* ⟨a + 6 * k + 2, 3 * k + 3, 0, 0, 0⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 3 * k + 1 = 0 + (3 * k + 1) from by ring]
    have := r3r1_chain (3 * k + 1) a 1 0
    rw [show a + 2 * (3 * k + 1) = a + 6 * k + 2 from by ring,
        show 1 + 1 + (3 * k + 1) = 3 * k + 3 from by ring] at this
    exact this
  -- b_to_d: -> (a+6*k+2, 0, 0, 3*k+3, 0)
  have h4 : ⟨a + 6 * k + 2, 3 * k + 3, 0, 0, 0⟩ [fm]⊢* ⟨a + 6 * k + 2, 0, 0, 3 * k + 3, 0⟩ := by
    have := b_to_d (3 * k + 3) (a + 6 * k + 2) 0
    rw [show 0 + (3 * k + 3) = 3 * k + 3 from by ring] at this
    exact this
  -- d_to_e: -> (a+6*k+2, 0, 0, 0, 3*k+3)
  have h5 : ⟨a + 6 * k + 2, 0, 0, 3 * k + 3, 0⟩ [fm]⊢* ⟨a + 6 * k + 2, 0, 0, 0, 3 * k + 3⟩ := by
    have := d_to_e (3 * k + 3) (a + 6 * k + 2) 0
    rw [show 0 + (3 * k + 3) = 3 * k + 3 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus (step_stepStar_stepPlus h2 h3)
      (stepStar_trans h4 h5))

-- Odd transition: (a+k+1, 0, 0, 0, 2*k+1) ->+ (a+6*k+4, 0, 0, 0, 3*k+3)
theorem odd_trans (k a : ℕ) : ⟨a + k + 1, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨a + 6 * k + 4, 0, 0, 0, 3 * k + 3⟩ := by
  -- Drain k rounds: -> (a+1, 0, 3*k, 0, 1)
  have h1 : ⟨a + k + 1, 0, 0, 0, 2 * k + 1⟩ [fm]⊢* ⟨a + 1, 0, 3 * k, 0, 1⟩ := by
    rw [show a + k + 1 = (a + 1) + k from by ring,
        show 2 * k + 1 = 1 + 2 * k from by ring,
        show 3 * k = 0 + 3 * k from by ring]
    exact r5r2r2_drain k (a + 1) 0 1
  -- 4 steps: R5, R2, R3, R1 -> (a+2, 2, 3*k+1, 0, 0)
  have h2 : ⟨a + 1, 0, 3 * k, 0, 1⟩ [fm]⊢⁺ ⟨a + 2, 2, 3 * k + 1, 0, 0⟩ := by
    rw [show a + 1 = a + 1 from rfl,
        show a + 2 = a + 2 from rfl]
    exact odd_4step a (3 * k)
  -- R3+R1 chain (3*k+1) rounds: -> (a+6*k+4, 3*k+3, 0, 0, 0)
  have h3 : ⟨a + 2, 2, 3 * k + 1, 0, 0⟩ [fm]⊢* ⟨a + 6 * k + 4, 3 * k + 3, 0, 0, 0⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 3 * k + 1 = 0 + (3 * k + 1) from by ring]
    have := r3r1_chain (3 * k + 1) (a + 2) 1 0
    rw [show a + 2 + 2 * (3 * k + 1) = a + 6 * k + 4 from by ring,
        show 1 + 1 + (3 * k + 1) = 3 * k + 3 from by ring] at this
    exact this
  -- b_to_d + d_to_e drains
  have h4 : ⟨a + 6 * k + 4, 3 * k + 3, 0, 0, 0⟩ [fm]⊢* ⟨a + 6 * k + 4, 0, 0, 3 * k + 3, 0⟩ := by
    have := b_to_d (3 * k + 3) (a + 6 * k + 4) 0
    rw [show 0 + (3 * k + 3) = 3 * k + 3 from by ring] at this
    exact this
  have h5 : ⟨a + 6 * k + 4, 0, 0, 3 * k + 3, 0⟩ [fm]⊢* ⟨a + 6 * k + 4, 0, 0, 0, 3 * k + 3⟩ := by
    have := d_to_e (3 * k + 3) (a + 6 * k + 4) 0
    rw [show 0 + (3 * k + 3) = 3 * k + 3 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩)
  · execute fm 9
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 1 ∧ 2 * a ≥ e + 1)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show k + k = 2 * k from by ring] at hk; subst hk
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨⟨m + 6 * k + 2, 0, 0, 0, 3 * k + 3⟩,
        ⟨m + 6 * k + 2, 3 * k + 3, rfl, by omega, by omega⟩,
        even_trans k m⟩
    · subst hk
      obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨⟨m + 6 * k + 4, 0, 0, 0, 3 * k + 3⟩,
        ⟨m + 6 * k + 4, 3 * k + 3, rfl, by omega, by omega⟩,
        odd_trans k m⟩
  · exact ⟨2, 3, rfl, by omega, by omega⟩
