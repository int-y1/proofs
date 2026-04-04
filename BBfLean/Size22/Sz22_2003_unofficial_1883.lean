import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1883: [9/35, 5/33, 28/3, 121/7, 21/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 2 -1  0  1  0
 0  0  0 -1  2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1883

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem r4_drain : ∀ k d, ⟨a, 0, 0, d + k, 0⟩ [fm]⊢* ⟨a, 0, 0, d, 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1))
    step fm; ring_nf; finish

theorem spiral_round : ⟨a + 1, 0, c, 0, e + 3⟩ [fm]⊢* ⟨a, 0, c + 2, 0, e⟩ := by
  rcases c with _ | c'
  · step fm; step fm; step fm; step fm; step fm; finish
  · apply stepStar_trans (show ⟨a + 1, 0, c' + 1, 0, e + 3⟩ [fm]⊢* ⟨a, 0, c' + 3, 0, e⟩ from by
      step fm; step fm; step fm; step fm; step fm; finish)
    ring_nf; finish

theorem spiral_main : ∀ n, ∀ a c, ⟨a + n, 0, c, 0, 3 * n + r⟩ [fm]⊢* ⟨a, 0, c + 2 * n, 0, r⟩ := by
  intro n; induction' n with n ih <;> intro a c
  · simp; exists 0
  · rw [show 3 * (n + 1) + r = (3 * n + r) + 3 from by ring,
        show a + (n + 1) = a + n + 1 from by ring]
    apply stepStar_trans (spiral_round (a := a + n) (c := c) (e := 3 * n + r))
    apply stepStar_trans (ih a (c + 2))
    ring_nf; finish

theorem spiral_end_1 : ⟨a + 1, 0, c, 0, 1⟩ [fm]⊢* ⟨a, 2, c, 0, 0⟩ := by
  rcases c with _ | c'
  · step fm; step fm; step fm; finish
  · step fm; step fm; step fm; finish

theorem spiral_end_2 : ⟨a + 1, 0, c, 0, 2⟩ [fm]⊢* ⟨a, 1, c + 1, 0, 0⟩ := by
  rcases c with _ | c'
  · step fm; step fm; step fm; step fm; finish
  · apply stepStar_trans (show ⟨a + 1, 0, c' + 1, 0, 2⟩ [fm]⊢* ⟨a, 1, c' + 2, 0, 0⟩ from by
      step fm; step fm; step fm; step fm; finish)
    ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ a b,
    ⟨a, b + 1, c + k, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, b + k + 1, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · simp; exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring]
    step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (b + 1))
    ring_nf; finish

theorem r3_drain0 : ∀ k, ∀ a d,
    ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) (d + 1))
    ring_nf; finish

theorem phase_b : ∀ b c, ⟨a, b + 1, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * b + 4 * c + 2, 0, 0, b + c + 1, 0⟩ := by
  intro b c; rcases c with _ | c'
  · step fm
    apply stepStar_trans (r3_drain0 b (a + 2) 1)
    ring_nf; finish
  · rw [show c' + 1 = 0 + (c' + 1) from by ring]
    step fm; step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (r3r1_chain (c := 0) c' (a + 2) (b + 1))
    rw [show (b + 1) + c' + 1 = b + c' + 2 from by ring,
        show (a + 2) + 2 * c' = a + 2 * c' + 2 from by ring]
    apply stepStar_trans (r3_drain0 (b + c' + 2) (a + 2 * c' + 2) 0)
    ring_nf; finish

theorem phase_b0 : ⟨a + 1, 0, c + 1, 0, 0⟩ [fm]⊢* ⟨a + 4 * c + 6, 0, 0, c + 3, 0⟩ := by
  step fm; step fm
  show ⟨a, 2 + 1, c, 0, 0⟩ [fm]⊢* _
  apply stepStar_trans (phase_b 2 c)
  ring_nf; finish

theorem phase_b1 : ⟨a, 1, c, 0, 0⟩ [fm]⊢* ⟨a + 4 * c + 2, 0, 0, c + 1, 0⟩ := by
  show ⟨a, 0 + 1, c, 0, 0⟩ [fm]⊢* _
  apply stepStar_trans (phase_b 0 c)
  ring_nf; finish

theorem phase_b2 : ⟨a, 2, c, 0, 0⟩ [fm]⊢* ⟨a + 4 * c + 4, 0, 0, c + 2, 0⟩ := by
  show ⟨a, 1 + 1, c, 0, 0⟩ [fm]⊢* _
  apply stepStar_trans (phase_b 1 c)
  ring_nf; finish

theorem trans_mod0 : ⟨a + 2 * j + 3, 0, 0, 3 * (j + 1), 0⟩ [fm]⊢⁺
    ⟨a + 16 * j + 18, 0, 0, 4 * j + 6, 0⟩ := by
  apply stepStar_stepPlus
  · rw [show 3 * (j + 1) = 0 + (3 * (j + 1)) from by ring]
    apply stepStar_trans (r4_drain (3 * (j + 1)) 0)
    rw [show 2 * (3 * (j + 1)) = 3 * (2 * j + 2) + 0 from by ring,
        show a + 2 * j + 3 = (a + 1) + (2 * j + 2) from by ring]
    apply stepStar_trans (spiral_main (r := 0) (2 * j + 2) (a + 1) 0)
    rw [show 0 + 2 * (2 * j + 2) = (4 * j + 3) + 1 from by ring]
    apply stepStar_trans (phase_b0 (a := a) (c := 4 * j + 3))
    ring_nf; finish
  · intro h; have := congr_arg Prod.fst h; simp at this; omega

theorem trans_mod1 : ⟨a + 2 * j + 1, 0, 0, 3 * j + 1, 0⟩ [fm]⊢⁺
    ⟨a + 16 * j + 6, 0, 0, 4 * j + 2, 0⟩ := by
  apply stepStar_stepPlus
  · rw [show 3 * j + 1 = 0 + (3 * j + 1) from by ring]
    apply stepStar_trans (r4_drain (3 * j + 1) 0)
    rw [show 2 * (3 * j + 1) = 3 * (2 * j) + 2 from by ring,
        show a + 2 * j + 1 = (a + 1) + (2 * j) from by ring]
    apply stepStar_trans (spiral_main (r := 2) (2 * j) (a + 1) 0)
    rw [show 0 + 2 * (2 * j) = 4 * j from by ring]
    apply stepStar_trans (spiral_end_2 (a := a) (c := 4 * j))
    apply stepStar_trans (phase_b1 (a := a) (c := 4 * j + 1))
    ring_nf; finish
  · intro h; have := congr_arg Prod.fst h; simp at this; omega

theorem trans_mod2 : ⟨a + 2 * j + 2, 0, 0, 3 * j + 2, 0⟩ [fm]⊢⁺
    ⟨a + 16 * j + 12, 0, 0, 4 * j + 4, 0⟩ := by
  apply stepStar_stepPlus
  · rw [show 3 * j + 2 = 0 + (3 * j + 2) from by ring]
    apply stepStar_trans (r4_drain (3 * j + 2) 0)
    rw [show 2 * (3 * j + 2) = 3 * (2 * j + 1) + 1 from by ring,
        show a + 2 * j + 2 = (a + 1) + (2 * j + 1) from by ring]
    apply stepStar_trans (spiral_main (r := 1) (2 * j + 1) (a + 1) 0)
    rw [show 0 + 2 * (2 * j + 1) = 4 * j + 2 from by ring]
    apply stepStar_trans (spiral_end_1 (a := a) (c := 4 * j + 2))
    apply stepStar_trans (phase_b2 (a := a) (c := 4 * j + 2))
    ring_nf; finish
  · intro h; have := congr_arg Prod.fst h; simp at this; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ d ∧ d ≥ 2)
  · intro q ⟨A, D, hq, hA, hD⟩; subst hq
    obtain ⟨j, rfl | rfl | rfl⟩ : ∃ j, D = 3 * j ∨ D = 3 * j + 1 ∨ D = 3 * j + 2 :=
      ⟨D / 3, by omega⟩
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, A = m + 2 * j' + 3 := ⟨A - 2 * j' - 3, by omega⟩
      exact ⟨_, ⟨m + 16 * j' + 18, 4 * j' + 6, rfl, by omega, by omega⟩,
        trans_mod0 (a := m) (j := j')⟩
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, A = m + 2 * (j' + 1) + 1 := ⟨A - 2 * (j' + 1) - 1, by omega⟩
      exact ⟨_, ⟨m + 16 * (j' + 1) + 6, 4 * (j' + 1) + 2, rfl, by omega, by omega⟩,
        trans_mod1 (a := m) (j := j' + 1)⟩
    · obtain ⟨m, rfl⟩ : ∃ m, A = m + 2 * j + 2 := ⟨A - 2 * j - 2, by omega⟩
      exact ⟨_, ⟨m + 16 * j + 12, 4 * j + 4, rfl, by omega, by omega⟩,
        trans_mod2 (a := m) (j := j)⟩
  · exact ⟨2, 2, rfl, by omega, by omega⟩
