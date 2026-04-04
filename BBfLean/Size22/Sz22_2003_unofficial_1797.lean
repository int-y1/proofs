import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1797: [9/10, 5/21, 4/33, 77/2, 6/7]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  0
 2 -1  0  0 -1
-1  0  0  1  1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1797

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 1))
    ring_nf; finish

theorem r3_drain : ∀ k a, ⟨a, k, 0, 0, k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, 0⟩ := by
  intro k; induction' k with k ih
  · intro a; exists 0
  · intro a
    step fm
    apply stepStar_trans (ih (a + 2))
    ring_nf; finish

theorem cascade_round : ⟨1, b, 2 * j + 2, 0, e + 1⟩ [fm]⊢*
    ⟨1, b + 3, 2 * j, 0, e⟩ := by
  rw [show 2 * j + 2 = 2 * j + 1 + 1 from by ring]
  step fm
  step fm
  rw [show 2 * j + 1 = (2 * j) + 1 from by ring]
  step fm
  ring_nf; finish

theorem cascade_iter : ∀ m b e, ⟨1, b, 2 * m, 0, e + m⟩ [fm]⊢*
    ⟨1, b + 3 * m, 0, 0, e⟩ := by
  intro m; induction' m with m ih
  · intro b e; exists 0
  · intro b e
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring,
        show e + (m + 1) = (e + m) + 1 from by ring]
    apply stepStar_trans (cascade_round (j := m) (b := b) (e := e + m))
    apply stepStar_trans (ih (b + 3) e)
    ring_nf; finish

theorem spiral_round : ⟨0, 0, 2 * j + 2, d + 4, e⟩ [fm]⊢*
    ⟨0, 0, 2 * j + 4, d, e⟩ := by
  rw [show d + 4 = d + 3 + 1 from by ring]
  step fm
  rw [show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
  step fm
  rw [show d + 3 = (d + 2) + 1 from by ring]
  step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  step fm
  rw [show 2 * j + 4 = 2 * j + 2 + 2 from by ring]
  finish

theorem spiral_iter : ∀ k d e, ⟨0, 0, 2, d + 4 * k, e⟩ [fm]⊢*
    ⟨0, 0, 2 * k + 2, d, e⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e
    rw [show d + 4 * (k + 1) = (d + 4) + 4 * k from by ring]
    apply stepStar_trans (ih (d + 4) e)
    apply stepStar_trans (spiral_round (j := k) (d := d) (e := e))
    rw [show 2 * k + 4 = 2 * (k + 1) + 2 from by ring]
    finish

theorem initial_5 : ⟨0, 0, 0, d + 5, d + 5⟩ [fm]⊢* ⟨0, 0, 2, d + 1, d + 5⟩ := by
  rw [show d + 5 = (d + 4) + 1 from by ring]
  step fm
  rw [show d + 4 = (d + 3) + 1 from by ring]
  step fm
  step fm
  rw [show d + 3 = (d + 2) + 1 from by ring]
  step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  finish

theorem partial_round : ⟨0, 0, 2 * j + 2, 3, e⟩ [fm]⊢*
    ⟨0, 1, 2 * j + 3, 0, e⟩ := by
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show 2 * j + 2 = (2 * j + 1) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  ring_nf; finish

theorem case1_m0 : ⟨0, 0, 0, 1, 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 3, 3⟩ := by
  execute fm 5

theorem case1 (m : ℕ) : ⟨0, 0, 0, 4 * m + 5, 4 * m + 5⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * m + 9, 6 * m + 9⟩ := by
  apply stepStar_stepPlus_stepPlus (initial_5 (d := 4 * m))
  rw [show 4 * m + 1 = 1 + 4 * m from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_iter m 1 (4 * m + 5))
  rw [show 2 * m + 2 = 2 * m + 2 from rfl,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show 4 * m + 5 = (3 * m + 4) + (m + 1) from by ring,
      show 2 * m + 2 = 2 * (m + 1) from by ring]
  apply stepStar_trans (cascade_iter (m + 1) 1 (3 * m + 4))
  rw [show 1 + 3 * (m + 1) = 3 * m + 4 from by ring]
  apply stepStar_trans (r3_drain (3 * m + 4) 1)
  rw [show 1 + 2 * (3 * m + 4) = 6 * m + 9 from by ring]
  have h := r4_chain (6 * m + 9) 0 0 0
  simp only [Nat.zero_add] at h
  exact h

theorem case3_m0 : ⟨0, 0, 0, 3, 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 5, 5⟩ := by
  execute fm 13

theorem case3 (m : ℕ) : ⟨0, 0, 0, 4 * m + 7, 4 * m + 7⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * m + 11, 6 * m + 11⟩ := by
  rw [show 4 * m + 7 = (4 * m + 2) + 5 from by ring]
  apply stepStar_stepPlus_stepPlus (initial_5 (d := 4 * m + 2))
  rw [show 4 * m + 2 + 1 = 3 + 4 * m from by ring,
      show (4 * m + 2) + 5 = 4 * m + 7 from by ring]
  apply stepStar_stepPlus_stepPlus (spiral_iter m 3 (4 * m + 7))
  rw [show 2 * m + 2 = 2 * m + 2 from rfl]
  apply stepStar_stepPlus_stepPlus (partial_round (j := m) (e := 4 * m + 7))
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring,
      show 4 * m + 7 = (4 * m + 6) + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (2 * m + 2) + 1 = (2 * m + 2) + 1 from rfl]
  step fm
  rw [show 2 * m + 2 = 2 * (m + 1) from by ring,
      show 4 * m + 6 = (3 * m + 5) + (m + 1) from by ring]
  apply stepStar_trans (cascade_iter (m + 1) 2 (3 * m + 5))
  rw [show 2 + 3 * (m + 1) = 3 * m + 5 from by ring]
  apply stepStar_trans (r3_drain (3 * m + 5) 1)
  rw [show 1 + 2 * (3 * m + 5) = 6 * m + 11 from by ring]
  have h := r4_chain (6 * m + 11) 0 0 0
  simp only [Nat.zero_add] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d, q = ⟨0, 0, 0, d, d⟩ ∧ d ≥ 1 ∧ d % 2 = 1)
  · intro c ⟨d, hq, hd, hodd⟩; subst hq
    rcases d with _ | d
    · omega
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · subst hm
        rcases m with _ | m
        · exact ⟨⟨0, 0, 0, 3, 3⟩, ⟨3, rfl, by omega, by omega⟩, case1_m0⟩
        · have heq1 : m + 1 + (m + 1) + (m + 1 + (m + 1)) + 1 = 4 * m + 5 := by omega
          rw [heq1]
          exact ⟨⟨0, 0, 0, 6 * m + 9, 6 * m + 9⟩,
            ⟨6 * m + 9, rfl, by omega, by omega⟩, case1 m⟩
      · subst hm
        rcases m with _ | m
        · exact ⟨⟨0, 0, 0, 5, 5⟩, ⟨5, rfl, by omega, by omega⟩, case3_m0⟩
        · have heq3 : 2 * (m + 1) + 1 + (2 * (m + 1) + 1) + 1 = 4 * m + 7 := by omega
          rw [heq3]
          exact ⟨⟨0, 0, 0, 6 * m + 11, 6 * m + 11⟩,
            ⟨6 * m + 11, rfl, by omega, by omega⟩, case3 m⟩
    · omega
  · exact ⟨1, rfl, by omega, by omega⟩
