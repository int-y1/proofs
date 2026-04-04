import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1982: [99/35, 338/5, 5/39, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  1  0
 1  0 -1  0  0  2
 0 -1  1  0  0 -1
 0  0  0  1 -1  0
-1  0  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1982

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+2⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | _ => none

-- R4 repeated: move e to d
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

-- R1+R3 interleaved chain: k rounds
theorem r1r3_chain : ∀ k, ∀ a b e, ⟨a, b, 1, k, e, f + k⟩ [fm]⊢* ⟨a, b + k, 1, 0, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

-- R2R3 drain + final R2: (a, k+1, 1, 0, e, g+1) →⁺ (a+k+2, 0, 0, 0, e, g+k+4)
theorem drain : ∀ k, ∀ a e g, ⟨a, k + 1, 1, 0, e, g + 1⟩ [fm]⊢⁺ ⟨a + k + 2, 0, 0, 0, e, g + k + 4⟩ := by
  intro k; induction' k with k ih <;> intro a e g
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    rw [show g + 1 + 1 = (g + 1) + 1 from by ring]
    apply stepStar_trans (stepPlus_stepStar (ih (a + 1) e (g + 1)))
    ring_nf; finish

-- Main transition
theorem main_trans : ⟨a + 1, 0, 0, 0, n + 1, 2 * n + 2⟩ [fm]⊢⁺ ⟨a + n + 2, 0, 0, 0, n + 2, 2 * n + 4⟩ := by
  -- Phase 1: R4, move n+1 to d
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_d (n + 1) 0 (a := a + 1) (e := 0) (f := 2 * n + 2))
  rw [show 0 + (n + 1) = n + 1 from by ring]
  -- Phase 2: R5
  step fm
  -- Phase 3: R1+R3 chain
  rw [show (2 : ℕ) * n + 2 = (n + 1) + (n + 1) from by omega]
  apply stepStar_trans (r1r3_chain (n + 1) a 0 1 (f := n + 1))
  -- State: (a, 0+(n+1), 1, 0, 1+(n+1), n+1)
  rw [show 1 + (n + 1) = n + 2 from by ring]
  simp only [Nat.zero_add]
  -- State: (a, n+1, 1, 0, n+2, n+1)
  -- Apply drain with k = n
  rw [show n + 1 = n + 0 + 1 from by ring]
  have h := drain n a (n + 2) n
  rw [show n + n + 4 = 2 * n + 4 from by ring] at h
  exact stepPlus_stepStar h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 1, 2⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + 1, 0, 0, 0, e + 1, 2 * e + 2⟩) ⟨0, 0⟩
  intro ⟨a, e⟩; exact ⟨⟨a + e + 1, e + 1⟩, main_trans⟩
