import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1779: [9/10, 343/2, 22/21, 5/11, 6/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  3  0
 1 -1  0 -1  1
 0  0  1  0 -1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1779

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 chain: move e to c.
theorem e_to_c : ∀ k, ∀ c e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

-- R3/R1 interleaving.
theorem r3r1_chain : ∀ k, ∀ b c d e, ⟨0, b + 1, c + k, d + k, e⟩ [fm]⊢* ⟨0, b + 1 + k, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) c d (e + 1))
    ring_nf; finish

-- R3/R2 drain.
theorem r3r2_chain : ∀ k, ∀ b d e, ⟨0, b + k, 0, d + 1, e⟩ [fm]⊢* ⟨0, b, 0, d + 1 + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    step fm
    rw [show d + 3 = (d + 2) + 1 from by ring]
    apply stepStar_trans (ih b (d + 2) (e + 1))
    ring_nf; finish

-- Compose phases for e >= 1 case.
theorem phase2 : ⟨0, 0, e + 1, (e + f + 3) + 1, 0⟩ [fm]⊢⁺ ⟨0, (e + 3), 0, f + 3, e⟩ := by
  step fm  -- R5
  step fm  -- R1
  -- Goal: (0, 3, e, e+f+3, 0) ⊢* (0, e+3, 0, f+3, e)
  have h := r3r1_chain e 2 0 (f + 3) 0
  -- h : (0, 3, 0+e, (f+3)+e, 0) ⊢* (0, 3+e, 0, f+3, 0+e)
  simp only [Nat.zero_add] at h
  -- h : (0, 3, e, (f+3)+e, 0) ⊢* (0, 3+e, 0, f+3, e)
  rw [show e + f + 3 = (f + 3) + e from by ring]
  apply stepStar_trans h
  rw [show 3 + e = e + 3 from by ring]
  finish

-- Main transition for e >= 1: (0, 0, 0, e+f+4, e+1) ⊢⁺ (0, 0, 0, 2*e+f+9, 2*e+3)
theorem main_trans_succ : ⟨0, 0, 0, e + f + 4, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * e + f + 9, 2 * e + 3⟩ := by
  -- Phase 1: e_to_c
  rw [show (e + 1 : ℕ) = 0 + (e + 1) from by ring,
      show e + f + 4 = (e + f + 3) + 1 from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact e_to_c (e + 1) 0 0 (d := (e + f + 3) + 1)
  -- After e_to_c: (0, 0, 0+(e+1), (e+f+3)+1, 0)
  -- Need to match phase2's input: (0, 0, e+1, (e+f+3)+1, 0)
  rw [show 0 + (e + 1) = e + 1 from by ring]
  -- Phase 2: R5 + R1 + r3r1_chain
  apply stepPlus_stepStar_stepPlus (phase2 (e := e) (f := f))
  -- Phase 3: r3r2_chain
  rw [show (e + 3 : ℕ) = 0 + (e + 3) from by ring,
      show f + 3 = (f + 2) + 1 from by ring]
  apply stepStar_trans (r3r2_chain (e + 3) 0 (f + 2) e)
  ring_nf; finish

-- Main transition for e = 0: (0, 0, 0, f+3, 0) ⊢⁺ (0, 0, 0, f+7, 1)
theorem main_trans_zero : ⟨0, 0, 0, f + 3, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, f + 7, 1⟩ := by
  rw [show f + 3 = (f + 2) + 1 from by ring]
  step fm
  step fm
  -- Now at (0, 1, 0, f+5, 0)
  show ⟨0, 0 + 1, 0, (f + 4) + 1, 0⟩ [fm]⊢* ⟨0, 0, 0, f + 7, 1⟩
  apply stepStar_trans (r3r2_chain 1 0 (f + 4) 0)
  ring_nf; finish

-- Combined main transition.
theorem main_trans : ∀ f e, ⟨0, 0, 0, e + f + 3, e⟩ [fm]⊢⁺ ⟨0, 0, 0, (2 * e + 1) + (f + 3) + 3, 2 * e + 1⟩ := by
  intro f e; rcases e with _ | e
  · rw [show 0 + f + 3 = f + 3 from by ring,
        show (2 * 0 + 1) + (f + 3) + 3 = f + 7 from by ring,
        show 2 * 0 + 1 = 1 from by ring]
    exact main_trans_zero
  · rw [show (e + 1) + f + 3 = e + f + 4 from by ring,
        show (2 * (e + 1) + 1) + (f + 3) + 3 = 2 * e + f + 9 from by ring,
        show 2 * (e + 1) + 1 = 2 * e + 3 from by ring]
    exact main_trans_succ

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0 + 0 + 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨f, e⟩ ↦ ⟨0, 0, 0, e + f + 3, e⟩) ⟨0, 0⟩
  intro ⟨f, e⟩; exact ⟨⟨f + 3, 2 * e + 1⟩, main_trans f e⟩
