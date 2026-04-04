import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1928: [9/70, 25/2, 44/15, 7/11, 3/5]

Vector representation:
```
-1  2 -1 -1  0
-1  0  2  0  0
 2 -1 -1  0  1
 0  0  0  1 -1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1928

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_d : ∀ k : ℕ, ∀ d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih
  · intro d; exists 0
  · intro d; step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

theorem round : ⟨0, b + 1, c + 3, d + 2, e⟩ [fm]⊢* ⟨0, b + 4, c, d, e + 1⟩ := by
  step fm; step fm; step fm; finish

theorem round_chain : ∀ k, ⟨0, b + 1, c + 3 * k, 2 * k, e⟩ [fm]⊢* ⟨0, b + 3 * k + 1, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show c + 3 * (k + 1) = c + 3 * k + 3 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    show ⟨0, b + 1, c + 3 * k + 3, 2 * k + 2, e⟩ [fm]⊢* _
    apply stepStar_trans round
    rw [show b + 4 = b + 3 + 1 from by ring]
    apply stepStar_trans (ih (b := b + 3) (c := c) (e := e + 1))
    ring_nf; finish

theorem round_odd : ⟨0, b + 1, c + 2, 1, e⟩ [fm]⊢* ⟨0, b + 2, c + 2, 0, e + 1⟩ := by
  step fm; step fm; step fm; finish

theorem spiral_odd : ∀ k, ⟨0, b + 1, c + 3 * k + 2, 2 * k + 1, e⟩ [fm]⊢* ⟨0, b + 3 * k + 2, c + 2, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exact round_odd
  · rw [show c + 3 * (k + 1) + 2 = c + 2 + 3 * k + 3 from by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring]
    show ⟨0, b + 1, c + 2 + 3 * k + 3, 2 * k + 1 + 2, e⟩ [fm]⊢* _
    apply stepStar_trans round
    rw [show b + 4 = b + 3 + 1 from by ring,
        show c + 2 + 3 * k = c + 3 * k + 2 from by ring]
    apply stepStar_trans (ih (b := b + 3) (c := c) (e := e + 1))
    ring_nf; finish

theorem drain_b : ∀ k, ⟨0, k, c + 1, 0, e⟩ [fm]⊢* ⟨0, 0, c + 3 * k + 1, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · step fm; step fm; step fm
    rw [show c + 4 = c + 3 + 1 from by ring]
    apply stepStar_trans (ih (c := c + 3) (e := e + 1))
    ring_nf; finish

theorem middle_even : ∀ k, ⟨0, 0, c + 3 * k + 1, 2 * k, 0⟩ [fm]⊢* ⟨0, 3 * k + 1, c, 0, k⟩ := by
  intro k
  rcases k with _ | k
  · step fm; finish
  · rw [show c + 3 * (k + 1) + 1 = c + 3 * (k + 1) + 1 from rfl]
    step fm
    show ⟨0, 1, c + 3 * (k + 1), 2 * (k + 1), 0⟩ [fm]⊢* _
    rw [show c + 3 * (k + 1) = c + 3 * k + 3 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring]
    show ⟨0, 1, c + 3 * k + 3, 2 * k + 2, 0⟩ [fm]⊢* _
    apply stepStar_trans round
    rw [show 0 + 4 = 3 + 1 from by ring]
    apply stepStar_trans (round_chain k (b := 3) (c := c) (e := 1))
    ring_nf; finish

theorem middle_odd : ∀ k, ⟨0, 0, c + 3 * k + 3, 2 * k + 1, 0⟩ [fm]⊢* ⟨0, 3 * k + 2, c + 2, 0, k + 1⟩ := by
  intro k
  rw [show c + 3 * k + 3 = c + 3 * k + 2 + 1 from by ring]
  step fm
  show ⟨0, 1, c + 3 * k + 2, 2 * k + 1, 0⟩ [fm]⊢* ⟨0, 3 * k + 2, c + 2, 0, k + 1⟩
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show 3 * k + 2 = 0 + 3 * k + 2 from by ring,
      show k + 1 = 0 + k + 1 from by ring]
  exact spiral_odd k (b := 0) (c := c) (e := 0)

-- Full even transition: (0, 0, c, 0, 2k) where c = G+4k+2
-- Phase 1: e_to_d(2k): → (0, 0, c, 2k, 0)
-- Phase 2: middle_even(k+1) for k>=1 or direct for k=0
-- Phase 3: drain_b
theorem trans_even : ∀ k,
    ⟨0, 0, G + 4 * k + 2, 0, 2 * k⟩ [fm]⊢⁺ ⟨0, 0, G + 10 * k + 4, 0, 4 * k + 1⟩ := by
  intro k
  rcases k with _ | k
  · step fm; step fm; step fm; step fm; finish
  · -- e = 2(k+1) >= 2
    apply stepStar_stepPlus_stepPlus
    · -- e_to_d: →* (0, 0, G+4(k+1)+2, 2(k+1), 0)
      rw [show (2 * (k + 1) : ℕ) = 2 * (k + 1) from rfl]
      exact e_to_d (2 * (k + 1)) 0 (c := G + 4 * (k + 1) + 2)
    · -- R5 then spiral then drain
      rw [show 0 + 2 * (k + 1) = 2 * (k + 1) from by ring,
          show G + 4 * (k + 1) + 2 = (G + k + 2) + 3 * (k + 1) + 1 from by ring]
      step fm
      show ⟨0, 1, (G + k + 2) + 3 * (k + 1), 2 * (k + 1), 0⟩ [fm]⊢* _
      rw [show (G + k + 2) + 3 * (k + 1) = (G + k + 2) + 3 * k + 3 from by ring,
          show 2 * (k + 1) = 2 * k + 2 from by ring]
      show ⟨0, 1, (G + k + 2) + 3 * k + 3, 2 * k + 2, 0⟩ [fm]⊢* _
      apply stepStar_trans round
      rw [show 0 + 4 = 3 + 1 from by ring]
      apply stepStar_trans (round_chain k (b := 3) (c := G + k + 2) (e := 1))
      rw [show 3 + 3 * k + 1 = 3 * k + 4 from by ring,
          show 1 + k = k + 1 from by ring,
          show G + k + 2 = (G + k + 1) + 1 from by ring]
      apply stepStar_trans (drain_b (3 * k + 4) (c := G + k + 1) (e := k + 1))
      ring_nf; finish

theorem trans_odd : ∀ k,
    ⟨0, 0, G + 4 * k + 4, 0, 2 * k + 1⟩ [fm]⊢⁺ ⟨0, 0, G + 10 * k + 9, 0, 4 * k + 3⟩ := by
  intro k
  apply stepStar_stepPlus_stepPlus
  · -- e_to_d: →* (0, 0, G+4k+4, 2k+1, 0)
    exact e_to_d (2 * k + 1) 0 (c := G + 4 * k + 4)
  · -- R5 then spiral_odd then drain
    rw [show 0 + (2 * k + 1) = 2 * k + 1 from by ring,
        show G + 4 * k + 4 = (G + k + 1) + 3 * k + 3 from by ring]
    step fm
    show ⟨0, 1, (G + k + 1) + 3 * k + 2, 2 * k + 1, 0⟩ [fm]⊢* _
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (spiral_odd k (b := 0) (c := G + k + 1) (e := 0))
    rw [show 0 + 3 * k + 2 = 3 * k + 2 from by ring,
        show G + k + 1 + 2 = (G + k + 2) + 1 from by ring,
        show 0 + k + 1 = k + 1 from by ring]
    apply stepStar_trans (drain_b (3 * k + 2) (c := G + k + 2) (e := k + 1))
    ring_nf; finish

theorem main_trans : ⟨0, 0, G + 2 * e + 2, 0, e⟩ [fm]⊢⁺ ⟨0, 0, G + e + 2 * (2 * e + 1) + 2, 0, 2 * e + 1⟩ := by
  rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    have h := trans_even k (G := G)
    rw [show G + 2 * (2 * k) + 2 = G + 4 * k + 2 from by ring,
        show G + 2 * k + 2 * (2 * (2 * k) + 1) + 2 = G + 10 * k + 4 from by ring,
        show 2 * (2 * k) + 1 = 4 * k + 1 from by ring]
    exact h
  · subst hk
    have h := trans_odd k (G := G)
    rw [show G + 2 * (2 * k + 1) + 2 = G + 4 * k + 4 from by ring,
        show G + (2 * k + 1) + 2 * (2 * (2 * k + 1) + 1) + 2 = G + 10 * k + 9 from by ring,
        show 2 * (2 * k + 1) + 1 = 4 * k + 3 from by ring]
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨G, e⟩ ↦ ⟨0, 0, G + 2 * e + 2, 0, e⟩) ⟨0, 0⟩
  intro ⟨G, e⟩
  refine ⟨⟨G + e, 2 * e + 1⟩, ?_⟩
  exact main_trans
