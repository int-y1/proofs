import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #46: [1/15, 6/77, 49/3, 5/49, 3993/2]

Vector representation:
```
 0 -1 -1  0  0
 1  1  0 -1 -1
 0 -1  0  2  0
 0  0  1 -2  0
-1  1  0  0  3
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_46

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+3⟩
  | _ => none

theorem r3_drain : ∀ k a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  step fm
  apply stepStar_trans (ih a (d + 2))
  ring_nf; finish

theorem r4_chain : ∀ k a c d, ⟨a, 0, c, d + 2 * k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + 2 * (k + 1) = d + 2 * k + 2 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1) d)
  ring_nf; finish

theorem r5r1_chain : ∀ k a c e, ⟨a + k, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a c (e + 3))
  ring_nf; finish

theorem r2r2r3_chain : ∀ k a b e,
    ⟨a, b, 0, 2, e + 2 * k⟩ [fm]⊢* ⟨a + 2 * k, b + k, 0, 2, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · simp; exists 0
  rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (a + 2) (b + 1) e)
  ring_nf; finish

theorem phase1_even (m a : ℕ) :
    ⟨a + 1, 0, 0, 0, 2 * m⟩ [fm]⊢⁺ ⟨a + 2 * m + 3, 0, 0, 2 * m + 5, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 2 * m⟩ = some ⟨a, 1, 0, 0, 2 * m + 3⟩; simp [fm]
  step fm
  apply stepStar_trans (c₂ := ⟨a + 2 * m, m, 0, 2, 3⟩)
  · have h := r2r2r3_chain m a 0 3
    rw [show 3 + 2 * m = 2 * m + 3 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  step fm; step fm; step fm; step fm
  have h := r3_drain (m + 2) (a + 2 * m + 3) 1
  rw [show 1 + 2 * (m + 2) = 2 * m + 5 from by ring] at h; exact h

theorem phase1_odd (m a : ℕ) :
    ⟨a + 1, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨a + 2 * m + 4, 0, 0, 2 * m + 6, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 2 * m + 1⟩ = some ⟨a, 1, 0, 0, 2 * m + 4⟩; simp [fm]
  step fm
  apply stepStar_trans (c₂ := ⟨a + 2 * (m + 2), m + 2, 0, 2, 0⟩)
  · have h := r2r2r3_chain (m + 2) a 0 0
    rw [show 0 + 2 * (m + 2) = 2 * m + 4 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  have h := r3_drain (m + 2) (a + 2 * (m + 2)) 2
  rw [show 2 + 2 * (m + 2) = 2 * m + 6 from by ring,
      show a + 2 * (m + 2) = a + 2 * m + 4 from by ring] at h; exact h

theorem phase2_even : ∀ k a, ⟨a + k, 0, 0, 2 * k, 0⟩ [fm]⊢* ⟨a, 0, 0, 0, 3 * k⟩ := by
  intro k a
  apply stepStar_trans (c₂ := ⟨a + k, 0, k, 0, 0⟩)
  · have h := r4_chain k (a + k) 0 0
    simp only [Nat.zero_add] at h; exact h
  have h := r5r1_chain k a 0 0
  simp only [Nat.zero_add] at h; exact h

theorem phase2_odd (k a : ℕ) :
    ⟨a + k + 1, 0, 0, 2 * k + 5, 0⟩ [fm]⊢* ⟨a + 1, 0, 0, 0, 3 * k + 2⟩ := by
  apply stepStar_trans (c₂ := ⟨a + k + 1, 0, k + 2, 1, 0⟩)
  · have h := r4_chain (k + 2) (a + k + 1) 0 1
    rw [show 1 + 2 * (k + 2) = 2 * k + 5 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  rw [show a + k + 1 = (a + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show a + k + 1 = (a + 1) + k from by ring]
  have h := r5r1_chain k (a + 1) 0 2
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_; ring_nf; finish

theorem full_even (a m : ℕ) :
    ⟨a + 1, 0, 0, 0, 2 * m⟩ [fm]⊢⁺ ⟨a + m + 3, 0, 0, 0, 3 * m + 2⟩ := by
  apply stepPlus_stepStar_stepPlus (phase1_even m a)
  have h := phase2_odd m (a + m + 2)
  rw [show a + m + 2 + m + 1 = a + 2 * m + 3 from by ring,
      show a + m + 2 + 1 = a + m + 3 from by ring] at h; exact h

theorem full_odd (a m : ℕ) :
    ⟨a + 1, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨a + m + 1, 0, 0, 0, 3 * m + 9⟩ := by
  apply stepPlus_stepStar_stepPlus (phase1_odd m a)
  have h := phase2_even (m + 3) (a + m + 1)
  rw [show a + m + 1 + (m + 3) = a + 2 * m + 4 from by ring,
      show 2 * (m + 3) = 2 * m + 6 from by ring,
      show 3 * (m + 3) = 3 * m + 9 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 2⟩) (by execute fm 14)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1)
  · intro c ⟨a, e, hq, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- e = 2m (even case)
      rw [hm]
      rw [show m + m = 2 * m from by ring]
      refine ⟨_, ⟨a - 1 + m + 3, 3 * m + 2, rfl, by omega⟩, ?_⟩
      rw [show a = (a - 1) + 1 from by omega]
      exact full_even (a - 1) m
    · -- e = 2m + 1 (odd case)
      rw [hm]
      rw [show 2 * m + 1 = 2 * m + 1 from rfl]
      refine ⟨_, ⟨a - 1 + m + 1, 3 * m + 9, rfl, by omega⟩, ?_⟩
      rw [show a = (a - 1) + 1 from by omega]
      exact full_odd (a - 1) m
  · exact ⟨3, 2, rfl, by omega⟩

end Sz22_2003_unofficial_46
