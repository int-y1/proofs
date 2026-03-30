import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #958: [4/15, 33/14, 325/2, 7/11, 21/13]

Vector representation:
```
 2 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  2  0  0  1
 0  0  0  1 -1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_958

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+2, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R3 drain: a into c (*2) and f, when b=0 and d=0.
theorem r3_drain : ∀ k, ∀ c e f, ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 2) e (f + 1))
    ring_nf; finish

-- R4 drain: e into d.
theorem r4_drain : ∀ k, ∀ c d f, ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

-- R1R2 chain: each round consumes 1 from c and 1 from d, adds 1 to a and 1 to e.
theorem r1r2_chain : ∀ k, ∀ a c d e f, ⟨a, 1, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + k, 1, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1) f)
    ring_nf; finish

theorem main_trans (n C F : ℕ) :
    ⟨n + 2, 0, C, 0, n, F⟩ [fm]⊢⁺ ⟨(n + 3 : ℕ), 0, C + n + 2, 0, n + 1, F + n + 1⟩ := by
  -- Phase 1: R3 drain (n+2 steps).
  apply stepStar_stepPlus_stepPlus (r3_drain (n + 2) C n F)
  -- Phase 2: R4 drain (n steps).
  rw [show C + 2 * (n + 2) = C + 2 * n + 4 from by ring,
      show F + (n + 2) = F + n + 2 from by ring]
  apply stepStar_stepPlus_stepPlus (r4_drain n (C + 2 * n + 4) 0 (F + n + 2))
  -- Phase 3: R5 fires once.
  rw [show (0 : ℕ) + n = n from by ring,
      show F + n + 2 = (F + n + 1) + 1 from by ring]
  step fm
  -- Phase 4: R1R2 chain (n+1 rounds).
  rw [show C + 2 * n + 4 = (C + n + 2) + (n + 1) + 1 from by ring,
      show n + 1 = 0 + (n + 1) from by ring]
  rw [show (C + n + 2) + (0 + (n + 1)) + 1 = ((C + n + 2) + 1) + (n + 1) from by ring]
  apply stepStar_trans (r1r2_chain (n + 1) 0 ((C + n + 2) + 1) 0 0 (F + n + 1))
  -- Phase 5: Final R1.
  step fm
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨n, C, F⟩ ↦ ⟨n + 2, 0, C, 0, n, F⟩) ⟨1, 0, 0⟩
  intro ⟨n, C, F⟩
  refine ⟨⟨n + 1, C + n + 2, F + n + 1⟩, ?_⟩
  exact main_trans n C F

end Sz22_2003_unofficial_958
