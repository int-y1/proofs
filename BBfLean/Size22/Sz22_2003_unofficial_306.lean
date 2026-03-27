import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #306: [15/2, 44/63, 1/165, 147/5, 1/3]

Vector representation:
```
-1  1  1  0  0
 2 -2  0 -1  1
 0 -1 -1  0 -1
 0  1 -1  2  0
 0 -1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_306

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a, b+2, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b+1, c+1, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | _ => none

-- Phase 1: R2+R1+R1 repeated k times
-- (0,2,c,d+k,e) →* (0,2,c+2*k,d,e+k)
theorem phase1 : ∀ k c e, ⟨0, 2, c, d+k, e⟩ [fm]⊢* (⟨0, 2, c+2*k, d, e+k⟩ : Q) := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c+2) (e+1))
    ring_nf; finish

-- Drain lemma: (0,0,2+2*k,d,k) →* (0,2,0,d+2*k+4,0)
theorem drain : ∀ k d, ⟨0, 0, 2+2*k, d, k⟩ [fm]⊢* (⟨0, 2, 0, d+2*k+4, 0⟩ : Q) := by
  intro k; induction k with
  | zero => intro d; step fm; step fm; ring_nf; finish
  | succ k ih =>
    intro d
    rw [show 2 + 2 * (k + 1) = (2 + 2 * k) + 1 + 1 from by ring]
    rw [show k + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (d + 2))
    ring_nf; finish

-- Phase 2: (0,2,2*(d+1),0,d+1) →⁺ (0,2,0,2*(d+1),0)
theorem phase2 : ∀ d, ⟨0, 2, 2*(d+1), 0, d+1⟩ [fm]⊢⁺ (⟨0, 2, 0, 2*(d+1), 0⟩ : Q) := by
  intro d; cases d with
  | zero => execute fm 2
  | succ d =>
    rw [show 2 * (d + 1 + 1) = (2 * d + 2) + 1 + 1 from by ring]
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    step fm; step fm
    rw [show 2 * d + 2 = 2 + 2 * d from by ring]
    apply stepStar_trans (drain d 0)
    ring_nf; finish

-- Full cycle: (0,2,0,D+1,0) →⁺ (0,2,0,2*(D+1),0)
theorem cycle : ∀ D, ⟨0, 2, 0, D+1, 0⟩ [fm]⊢⁺ (⟨0, 2, 0, 2*(D+1), 0⟩ : Q) := by
  intro D
  have h1 := phase1 (d := 0) (D+1) 0 0
  simp at h1
  apply stepStar_stepPlus_stepPlus h1
  exact phase2 D

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 2, 0⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D, q = ⟨0, 2, 0, D+1, 0⟩)
  · intro c ⟨D, hq⟩; subst hq
    exact ⟨⟨0, 2, 0, 2*(D+1), 0⟩, ⟨2*D+1, by ring_nf⟩, cycle D⟩
  · exact ⟨1, rfl⟩
