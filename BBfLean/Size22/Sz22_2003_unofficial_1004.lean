import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1004: [4/15, 63/2, 11/3, 25/77, 3/55]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0  1  0
 0 -1  0  0  1
 0  0  2 -1 -1
 0  1 -1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1004

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d+k, e+k) →* (0, 0, c+2*k, d, e)
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e + k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) d e)
    ring_nf; finish

-- R2 drain: (a+k, b, 0, d, e) →* (a, b+2*k, 0, d+k, e)
theorem r2_drain : ∀ k, ∀ a b d, ⟨a + k, b, 0, d, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) (d + 1))
    ring_nf; finish

-- R3 drain: (0, b+k, 0, d, e) →* (0, b, 0, d, e+k)
theorem r3_drain : ∀ k, ∀ b d e, ⟨0, b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

-- One R2/R1/R1 round: (a+1, 0, c+2, d, e) →* (a+4, 0, c, d+1, e)
theorem one_round : ⟨a + 1, 0, c + 2, d, e⟩ [fm]⊢* ⟨a + 4, 0, c, d + 1, e⟩ := by
  step fm
  step fm
  step fm
  finish

-- R2/R1/R1 chain: (a+1, 0, 2*k, d, e) →* (a+1+3*k, 0, 0, d+k, e)
theorem r2r1r1_chain : ∀ k, ∀ a d, ⟨a + 1, 0, 2 * k, d, e⟩ [fm]⊢* ⟨a + 1 + 3 * k, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    apply stepStar_trans (one_round (a := a) (c := 2 * k) (d := d) (e := e))
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (d + 1))
    ring_nf; finish

-- R5 + R1: (0, 0, c+2, 0, e+1) →* (2, 0, c, 0, e)
theorem r5_r1 : (⟨0, 0, c + 2, 0, e + 1⟩ : Q) [fm]⊢* ⟨2, 0, c, 0, e⟩ := by
  step fm
  step fm
  finish

-- Full transition: (0, 0, 0, d+1, e+d+2) ⊢⁺ (0, 0, 0, 4*d+2, e+6*d+4)
theorem full_transition (d e : ℕ) :
    (⟨0, 0, 0, d + 1, e + d + 2⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, 4 * d + 2, e + 6 * d + 4⟩ := by
  -- Phase 1: First R4 step (establishes ⊢⁺)
  rw [show e + d + 2 = (e + d + 1) + 1 from by ring]
  step fm
  -- State: (0, 0, 2, d, e+d+1)
  rw [show e + d + 1 = (e + 1) + d from by ring]
  -- Phase 2: Remaining R4 steps (d times)
  have h2 := r4_chain d 2 0 (e + 1)
  rw [Nat.zero_add] at h2
  apply stepStar_trans h2
  rw [show 2 + 2 * d = 2 * d + 2 from by ring]
  -- State: (0, 0, 2*d+2, 0, e+1)
  -- Phase 3: R5 + R1
  apply stepStar_trans (r5_r1 (c := 2 * d) (e := e))
  -- State: (2, 0, 2*d, 0, e)
  -- Phase 4: R2/R1/R1 chain (d rounds)
  have h4 := r2r1r1_chain d 1 0 (e := e)
  rw [Nat.zero_add, show 1 + 1 = (2 : ℕ) from by ring, show 1 + 1 + 3 * d = 3 * d + 2 from by ring] at h4
  apply stepStar_trans h4
  -- State: (3*d+2, 0, 0, d, e)
  -- Phase 5: R2 drain (3*d+2 steps)
  have h5 := r2_drain (3 * d + 2) 0 0 d (e := e)
  rw [Nat.zero_add, Nat.zero_add, show d + (3 * d + 2) = 4 * d + 2 from by ring,
      show 2 * (3 * d + 2) = 6 * d + 4 from by ring] at h5
  apply stepStar_trans h5
  -- State: (0, 6*d+4, 0, 4*d+2, e)
  -- Phase 6: R3 drain (6*d+4 steps)
  have h6 := r3_drain (6 * d + 4) 0 (4 * d + 2) e
  rw [Nat.zero_add] at h6
  apply stepStar_trans h6
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 1, e + d + 2⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  exact ⟨⟨4 * d + 1, e + 2 * d + 1⟩, by
    show (⟨0, 0, 0, d + 1, e + d + 2⟩ : Q) [fm]⊢⁺
      ⟨0, 0, 0, (4 * d + 1) + 1, (e + 2 * d + 1) + (4 * d + 1) + 2⟩
    rw [show (4 * d + 1) + 1 = 4 * d + 2 from by ring,
        show (e + 2 * d + 1) + (4 * d + 1) + 2 = e + 6 * d + 4 from by ring]
    exact full_transition d e⟩
