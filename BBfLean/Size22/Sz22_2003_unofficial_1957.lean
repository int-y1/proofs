import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1957: [9/70, 847/5, 5/33, 4/11, 5/2]

Vector representation:
```
-1  2 -1 -1  0
 0  0 -1  1  2
 0 -1  1  0 -1
 2  0  0  0 -1
-1  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1957

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem r5r1_chain : ∀ k a b d,
    ⟨a + 2 * k, b, 0, d + k, 0⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 2) d)
    ring_nf; finish

-- R3R2 drain: (0, k+1, 0, d, e+1) →* (0, 1, 0, d+k, e+k+1)
theorem r3r2_drain : ∀ k d e,
    ⟨0, k + 1, 0, d, e + 1⟩ [fm]⊢* ⟨0, 1, 0, d + k, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show (k + 1) + 1 = (k + 1) + 1 from rfl]
    step fm; step fm
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k a d,
    ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) d)
    ring_nf; finish

-- Main transition composed as a single chain.
theorem main_trans (d : ℕ) :
    ⟨2 * d + 4, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨4 * d + 8, 0, 0, 2 * d + 3, 0⟩ := by
  -- Phase 1: R5R1 chain (d+1) times: → (2, 2d+2, 0, 0, 0)
  have h1 : ⟨2 * d + 4, 0, 0, d + 1, 0⟩ [fm]⊢* ⟨2, 2 * d + 2, 0, 0, 0⟩ := by
    have h := r5r1_chain (d + 1) 2 0 0
    rw [show 2 + 2 * (d + 1) = 2 * d + 4 from by ring,
        show 0 + (d + 1) = d + 1 from by ring,
        show 0 + 2 * (d + 1) = 2 * d + 2 from by ring] at h
    exact h
  -- Phase 2: 6 steps → (0, 2d+2, 0, 1, 2)
  have h2 : ⟨2, 2 * d + 2, 0, 0, 0⟩ [fm]⊢⁺ ⟨0, 2 * d + 2, 0, 1, 2⟩ := by
    rw [show 2 * d + 2 = (2 * d + 1) + 1 from by ring]
    step fm; step fm
    rw [show 2 * d + 1 + 1 = (2 * d) + 1 + 1 from by ring]
    step fm; step fm
    rw [show 2 * d + 1 + 2 = (2 * d + 2) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 3: R3R2 drain (2d+1) rounds: (0, 2d+2, 0, 1, 2) →* (0, 1, 0, 2d+2, 2d+3)
  have h3 : ⟨0, 2 * d + 2, 0, 1, 2⟩ [fm]⊢* ⟨0, 1, 0, 2 * d + 2, 2 * d + 3⟩ := by
    have h := r3r2_drain (2 * d + 1) 1 1
    simp only [Nat.reduceAdd] at h
    -- h : (0, 2*d+1+1, 0, 1, 2) ⊢* (0, 1, 0, 1+(2*d+1), 1+(2*d+1)+1)
    -- after simp, the 1+1 → 2 happened. But 2*d+1+1 and 1+(2*d+1) remain.
    rw [show 1 + (2 * d + 1) + 1 = 2 * d + 3 from by ring,
        show 1 + (2 * d + 1) = 2 * d + 2 from by ring,
        show 2 * d + 1 + 1 = 2 * d + 2 from by ring] at h
    exact h
  -- Phase 4: Last R3R2: (0, 1, 0, 2d+2, 2d+3) →⁺ (0, 0, 0, 2d+3, 2d+4)
  have h4 : ⟨0, 1, 0, 2 * d + 2, 2 * d + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * d + 3, 2 * d + 4⟩ := by
    rw [show 2 * d + 3 = (2 * d + 2) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 5: R4 chain (2d+4) times: → (4d+8, 0, 0, 2d+3, 0)
  have h5 : ⟨0, 0, 0, 2 * d + 3, 2 * d + 4⟩ [fm]⊢* ⟨4 * d + 8, 0, 0, 2 * d + 3, 0⟩ := by
    have h := r4_chain (2 * d + 4) 0 (2 * d + 3)
    rw [show 0 + 2 * (2 * d + 4) = 4 * d + 8 from by ring] at h
    exact h
  exact stepPlus_stepStar_stepPlus
    (stepPlus_trans
      (stepPlus_stepStar_stepPlus (stepStar_stepPlus_stepPlus h1 h2) h3)
      h4)
    h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨2 * d + 4, 0, 0, d + 1, 0⟩) 0
  intro d; refine ⟨2 * d + 2, ?_⟩
  show ⟨2 * d + 4, 0, 0, d + 1, 0⟩ [fm]⊢⁺ ⟨2 * (2 * d + 2) + 4, 0, 0, (2 * d + 2) + 1, 0⟩
  have h := main_trans d
  rw [show 2 * (2 * d + 2) + 4 = 4 * d + 8 from by ring,
      show (2 * d + 2) + 1 = 2 * d + 3 from by ring]
  exact h
