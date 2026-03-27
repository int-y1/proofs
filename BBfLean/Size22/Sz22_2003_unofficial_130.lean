import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #130: [1/45, 1225/33, 6/7, 1/3, 99/2]

Vector representation:
```
 0 -2 -1  0  0
 0 -1  2  2 -1
 1  1  0 -1  0
 0 -1  0  0  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

---

The canonical state is `(a, 0, 0, 0, e)` with `a >= 1`. The transition splits by parity of `e`:
- `e = 0`: `(a, 0, 0, 0, 0) ->+ (a, 0, 0, 0, 1)` in 8 steps
- `e = 2k+1`: `(a, 0, 0, 0, 2k+1) ->+ (a+k+1, 0, 0, 0, 3k+2)`
- `e = 2(k+1)`: `(a, 0, 0, 0, 2(k+1)) ->+ (a+k+1, 0, 0, 0, 3k+4)`

Since `a` never decreases and `e` always increases, the machine never halts.
-/

namespace Sz22_2003_unofficial_130

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

private theorem tuple_eq {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ : ℕ}
    (h1 : a₁ = a₂) (h2 : b₁ = b₂) (h3 : c₁ = c₂) (h4 : d₁ = d₂) (h5 : e₁ = e₂) :
    (⟨a₁, b₁, c₁, d₁, e₁⟩ : Q) = ⟨a₂, b₂, c₂, d₂, e₂⟩ := by
  subst h1; subst h2; subst h3; subst h4; subst h5; rfl

-- Phase 1: R3+R2 interleaving
theorem phase1_loop : ∀ k a c d,
    ⟨a, 0, c, d+1, e+k⟩ [fm]⊢* ⟨a+k, 0, c+2*k, d+1+k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase 2 (even d): R3+R3+R1 loop
theorem phase2_even : ∀ k a c,
    ⟨a, 0, c+k, 2*k, 0⟩ [fm]⊢* ⟨a+2*k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 2 (odd d): R3+R3+R1 loop + R3+R4
theorem phase2_odd : ∀ k a c,
    ⟨a, 0, c+k, 2*k+1, 0⟩ [fm]⊢* ⟨a+2*k+1, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · -- base: (a, 0, c, 1, 0) → (a+1, 0, c, 0, 0) in 2 steps (R3+R4)
    step fm; step fm; finish
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- Phase 3: R5+R1 unwinding
theorem phase3_loop : ∀ k a e,
    ⟨a+k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- E=0 bootstrap: 8 steps
theorem e0_trans : ⟨a+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+1, 0, 0, 0, 1⟩ := by
  execute fm 8

-- Initial 3 steps for E>=1 (as stepPlus)
theorem initial_steps : ⟨a+1, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨a, 0, 4, 4, e⟩ := by
  step fm; step fm; step fm; finish

-- E odd main transition: (a+1, 0, 0, 0, 2*k+1) ->+ (a+k+2, 0, 0, 0, 3*k+2)
theorem odd_trans : ⟨a+1, 0, 0, 0, 2*k+1⟩ [fm]⊢⁺ ⟨a+k+2, 0, 0, 0, 3*k+2⟩ := by
  apply stepPlus_stepStar_stepPlus initial_steps
  -- Goal: (a, 0, 4, 4, 2*k) ⊢* (a+k+2, 0, 0, 0, 3*k+2)
  -- Phase 1: use phase1_loop with e=0, k:=2*k, c:=4, d:=3
  have h1 := phase1_loop (e := 0) (2*k) a 4 3
  simp only [Nat.zero_add] at h1
  -- h1: (a, 0, 4, 3+1, 2*k) ⊢* (a+2*k, 0, 4+2*(2*k), 3+1+2*k, 0)
  -- = (a, 0, 4, 4, 2*k) ⊢* (a+2*k, 0, 4+4*k, 4+2*k, 0) after normalization
  apply stepStar_trans h1
  -- Phase 2: d = 4+2*k = 2*(k+2) (even), c = 4+4*k = (3*k+2)+(k+2)
  have h2 := phase2_even (k+2) (a+2*k) (3*k+2)
  -- h2: (a+2*k, 0, (3*k+2)+(k+2), 2*(k+2), 0) ⊢* (a+2*k+2*(k+2), 0, 3*k+2, 0, 0)
  rw [show (⟨a+2*k, 0, 4+2*(2*k), 3+1+2*k, 0⟩ : Q) =
    ⟨a+2*k, 0, 3*k+2+(k+2), 2*(k+2), 0⟩ from tuple_eq rfl rfl (by ring) (by ring) rfl]
  apply stepStar_trans h2
  -- Phase 3
  have h3 := phase3_loop (3*k+2) (a+k+2) 0
  simp only [Nat.zero_add] at h3
  rw [show (⟨a+2*k+2*(k+2), 0, 3*k+2, 0, 0⟩ : Q) =
    ⟨a+k+2+(3*k+2), 0, 3*k+2, 0, 0⟩ from tuple_eq (by ring) rfl rfl rfl rfl]
  exact h3

-- E even main transition (k>=0): (a+1, 0, 0, 0, 2*(k+1)) ->+ (a+k+2, 0, 0, 0, 3*k+4)
theorem even_trans : ⟨a+1, 0, 0, 0, 2*(k+1)⟩ [fm]⊢⁺ ⟨a+k+2, 0, 0, 0, 3*k+4⟩ := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus initial_steps
  -- Goal: (a, 0, 4, 4, 2*k+1) ⊢* (a+k+2, 0, 0, 0, 3*k+4)
  -- Phase 1
  have h1 := phase1_loop (e := 0) (2*k+1) a 4 3
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  -- After phase1: (a+(2*k+1), 0, 4+2*(2*k+1), 3+1+(2*k+1), 0)
  -- d = 3+1+(2*k+1) = 4+2*k+1 = 2*k+5 = 2*(k+2)+1 (odd)
  -- c = 4+2*(2*k+1) = 4+4*k+2 = 4*k+6 = (3*k+4)+(k+2)
  have h2 := phase2_odd (k+2) (a+(2*k+1)) (3*k+4)
  rw [show (⟨a+(2*k+1), 0, 4+2*(2*k+1), 3+1+(2*k+1), 0⟩ : Q) =
    ⟨a+(2*k+1), 0, 3*k+4+(k+2), 2*(k+2)+1, 0⟩ from tuple_eq rfl rfl (by ring) (by ring) rfl]
  apply stepStar_trans h2
  -- After phase2: (a+(2*k+1)+2*(k+2)+1, 0, 3*k+4, 0, 0)
  -- Phase 3
  have h3 := phase3_loop (3*k+4) (a+k+2) 0
  simp only [Nat.zero_add] at h3
  rw [show (⟨a+(2*k+1)+2*(k+2)+1, 0, 3*k+4, 0, 0⟩ : Q) =
    ⟨a+k+2+(3*k+4), 0, 3*k+4, 0, 0⟩ from tuple_eq (by ring) rfl rfl rfl rfl]
  exact h3

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a+1, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    rcases e with _ | e
    · -- e = 0
      exact ⟨_, ⟨a, 1, rfl⟩, e0_trans⟩
    rcases e with _ | e
    · -- e = 1 (odd, k=0)
      exact ⟨⟨a+2, 0, 0, 0, 2⟩, ⟨a+1, 2, tuple_eq (by ring) rfl rfl rfl rfl⟩,
        by have := @odd_trans a 0; simp at this; exact this⟩
    rcases Nat.even_or_odd e with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- e = 2j, so e+2 = 2(j+1) (even)
      subst hj
      exact ⟨⟨a+j+2, 0, 0, 0, 3*j+4⟩, ⟨a+j+1, 3*j+4, tuple_eq (by ring) rfl rfl rfl rfl⟩,
        by rw [show (⟨a+1, 0, 0, 0, j+j+1+1⟩ : Q) = ⟨a+1, 0, 0, 0, 2*(j+1)⟩
              from tuple_eq rfl rfl rfl rfl (by ring)]
           exact even_trans⟩
    · -- e = 2j+1, so e+2 = 2(j+1)+1 (odd)
      subst hj
      exact ⟨⟨a+j+3, 0, 0, 0, 3*j+5⟩, ⟨a+j+2, 3*j+5, tuple_eq (by ring) rfl rfl rfl rfl⟩,
        by rw [show (⟨a+1, 0, 0, 0, 2*j+1+1+1⟩ : Q) = ⟨a+1, 0, 0, 0, 2*(j+1)+1⟩
              from tuple_eq rfl rfl rfl rfl (by ring)]
           have := @odd_trans a (j+1)
           rw [show a + (j + 1) + 2 = a + j + 3 from by ring,
               show 3 * (j + 1) + 2 = 3 * j + 5 from by ring] at this
           exact this⟩
  · exact ⟨0, 0, rfl⟩
