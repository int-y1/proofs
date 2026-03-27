import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #291: [14/15, 9/22, 625/2, 11/7, 3/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -1
-1  0  4  0  0
 0  0  0 -1  1
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_291

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+4, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem d_to_e : ∀ k c d e, ⟨0, 0, c, d+k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e+k⟩ := by
  intro k; induction k with
  | zero => intro c d e; exists 0
  | succ k ih =>
    intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    have h := ih c d (e + 1)
    rw [show e + 1 + k = e + (k + 1) from by ring] at h
    exact h

theorem a_to_c : ∀ k a c d, ⟨a+k, 0, c, d, 0⟩ [fm]⊢* ⟨a, (0 : ℕ), c+4*k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

theorem r1_chain : ∀ k a b c d e, ⟨a, b+k, c+k, d, e⟩ [fm]⊢* ⟨a+k, b, c, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro a b c d e; exists 0
  | succ k ih =>
    intro a b c d e
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _ _ _)
    ring_nf; finish

theorem mix_round : ∀ k A c d e, ⟨A+1, 0, c+2*k, d, e+k⟩ [fm]⊢* ⟨A+k+1, (0 : ℕ), c, d+2*k, e⟩ := by
  intro k; induction k with
  | zero => intro A c d e; simp; exists 0
  | succ k ih =>
    intro A c d e
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 0 + 2 from by ring,
        show c + 2 * k + 2 = (c + 2 * k) + 2 from by ring]
    apply stepStar_trans (r1_chain 2 _ _ _ _ _)
    rw [show A + 2 = (A + 1) + 1 from by ring]
    have h := ih (A + 1) c (d + 2) e
    rw [show A + 1 + k + 1 = A + (k + 1) + 1 from by ring,
        show d + 2 + 2 * k = d + 2 * (k + 1) from by ring] at h
    exact h

theorem main_trans (D : ℕ) :
    ⟨0, 0, 2*D+4, D, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 4*D+6, 2*D+1, 0⟩ := by
  -- Phase 1: d_to_e
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 2*D+4, 0, D⟩)
  · have h := d_to_e D (2*D+4) 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 2: R5
  apply step_stepStar_stepPlus (c₂ := ⟨0, 1, 2*D+3, 0, D⟩)
  · rw [show 2*D+4 = (2*D+3) + 1 from by ring]; simp [fm]
  -- Phase 3: R1 (one step)
  apply stepStar_trans (c₂ := ⟨1, 0, 2*D+2, 1, D⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring, show 2*D+3 = (2*D+2) + 1 from by ring]
    step fm; finish
  -- Phase 4: mix_round D
  apply stepStar_trans (c₂ := ⟨D+1, 0, 2, 2*D+1, 0⟩)
  · have h := mix_round D 0 2 1 0
    simp only [Nat.zero_add] at h
    rw [show 2 + 2 * D = 2 * D + 2 from by ring,
        show 1 + 2 * D = 2 * D + 1 from by ring] at h
    exact h
  -- Phase 5: a_to_c
  have h := a_to_c (D+1) 0 2 (2*D+1)
  simp only [Nat.zero_add] at h
  rw [show 2 + 4 * (D + 1) = 4*D+6 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D, q = ⟨0, 0, 2*D+4, D, 0⟩)
  · intro q ⟨D, hq⟩
    subst hq
    exact ⟨⟨0, 0, 4*D+6, 2*D+1, 0⟩,
           ⟨2*D+1, by ring_nf⟩,
           main_trans D⟩
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_291
