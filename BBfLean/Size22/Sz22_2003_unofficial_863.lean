import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #863: [4/105, 15/22, 147/2, 11/3, 2/7]

Vector representation:
```
 2 -1 -1 -1  0
-1  1  1  0 -1
-1  1  0  2  0
 0 -1  0  0  1
 1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_863

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R3 chain: drain a, fill b and d.
theorem r3_drain : ∀ k b d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b + k, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) (d + 2))
    ring_nf; finish

-- R4 chain: drain b, fill e.
theorem b_drain : ∀ k d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

-- R2+R1 chain: each step consumes 1 from e and d, adds 1 to a.
theorem r2r1_chain : ∀ e a d, ⟨a + 1, 0, 0, d + e, e⟩ [fm]⊢* ⟨a + 1 + e, 0, 0, d, 0⟩ := by
  intro e; induction' e with e ih <;> intro a d
  · exists 0
  · rw [show d + (e + 1) = (d + e) + 1 from by ring]
    step fm
    rw [show (d + e) + 1 = d + e + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) d)
    ring_nf; finish

-- R5 + R2+R1 chain.
theorem interleave : ∀ e d, ⟨0, 0, 0, d + e + 1, e⟩ [fm]⊢⁺ ⟨e + 1, 0, 0, d, 0⟩ := by
  intro e d
  rw [show d + e + 1 = (d + e) + 1 from by ring]
  step fm
  have h := r2r1_chain e 0 d
  simp only [Nat.zero_add] at h
  rw [show 1 + e = e + 1 from by ring] at h
  exact h

-- Main transition.
theorem main_step (a T : ℕ) :
    ⟨a + 2, 0, 0, T, 0⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, T + a + 1, 0⟩ := by
  -- Phase 1: R3 drain
  have phase1 : ⟨a + 2, 0, 0, T, 0⟩ [fm]⊢* ⟨0, a + 2, 0, T + 2 * (a + 2), 0⟩ := by
    have h := r3_drain (a := 0) (a + 2) 0 T
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 2: R4 drain
  have phase2 : ⟨0, a + 2, 0, T + 2 * (a + 2), 0⟩ [fm]⊢*
      ⟨0, 0, 0, T + 2 * (a + 2), a + 2⟩ := by
    have h := b_drain (b := 0) (a + 2) (T + 2 * (a + 2)) 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 3: interleave
  have phase3 : ⟨0, 0, 0, T + 2 * (a + 2), a + 2⟩ [fm]⊢⁺
      ⟨a + 3, 0, 0, T + a + 1, 0⟩ := by
    have h := interleave (a + 2) (T + a + 1)
    rw [show T + a + 1 + (a + 2) + 1 = T + 2 * (a + 2) from by ring] at h
    rw [show a + 2 + 1 = a + 3 from by ring] at h
    exact h
  exact stepStar_stepPlus_stepPlus (stepStar_trans phase1 phase2) phase3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, T⟩ ↦ ⟨a + 2, 0, 0, T, 0⟩) ⟨0, 0⟩
  intro ⟨a, T⟩; exact ⟨⟨a + 1, T + a + 1⟩, main_step a T⟩

end Sz22_2003_unofficial_863
