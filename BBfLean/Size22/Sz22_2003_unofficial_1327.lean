import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1327: [63/10, 2/33, 121/2, 5/7, 20/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 2  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1327

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d, e⟩
  | _ => none

-- R3 chain: drain a into e (b=0, c=0)
theorem r3_chain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), (0 : ℕ), d, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), (0 : ℕ), c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R2+R1 interleaved chain: each round R2 then R1, consuming c and e, building b and d
theorem r2r1_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b + 1, k, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + k + 1, (0 : ℕ), d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) (d + 1) e)
    ring_nf; finish

-- R2 chain: drain b into a (c=0)
theorem r2_chain : ∀ k, ∀ a d e,
    ⟨a, k, (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨a + k, (0 : ℕ), (0 : ℕ), d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) d e)
    ring_nf; finish

-- Main transition: (n+4, 0, 0, n+2, n) →⁺ (n+5, 0, 0, n+3, n+1)
theorem main_trans (n : ℕ) :
    ⟨n + 4, (0 : ℕ), (0 : ℕ), n + 2, n⟩ [fm]⊢⁺
    ⟨n + 5, (0 : ℕ), (0 : ℕ), n + 3, n + 1⟩ := by
  -- First R3 step: (n+4, 0, 0, n+2, n) → (n+3, 0, 0, n+2, n+2)
  apply step_stepStar_stepPlus
    (by simp [fm] : (⟨n + 4, 0, 0, n + 2, n⟩ : Q) [fm]⊢
      ⟨n + 3, 0, 0, n + 2, n + 2⟩)
  -- Phase 1 cont: R3 chain (n+3 more times)
  apply stepStar_trans (r3_chain (n + 3) (n + 2) (n + 2))
  rw [show n + 2 + 2 * (n + 3) = 3 * n + 8 from by ring]
  -- Phase 2: R4 chain (n+2 times)
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_trans (d_to_c (n + 2) 0 0 (3 * n + 8))
  rw [show 0 + (n + 2) = n + 2 from by ring]
  -- Phase 3: R5 step
  rw [show 3 * n + 8 = (3 * n + 7) + 1 from by ring]
  step fm
  -- State: (2, 0, n+3, 0, 3n+7)
  -- Phase 4: R1 twice
  step fm
  step fm
  -- State: (0, 4, n+1, 2, 3n+7)
  -- Phase 5: R2+R1 chain (n+1 times)
  rw [show 3 * n + 7 = (2 * n + 6) + (n + 1) from by ring]
  apply stepStar_trans (r2r1_chain (n + 1) 3 2 (2 * n + 6))
  rw [show 3 + (n + 1) + 1 = n + 5 from by ring,
      show 2 + (n + 1) = n + 3 from by ring]
  -- State: (0, n+5, 0, n+3, 2n+6)
  -- Phase 6: R2 chain (n+5 times)
  rw [show 2 * n + 6 = (n + 1) + (n + 5) from by ring]
  apply stepStar_trans (r2_chain (n + 5) 0 (n + 3) (n + 1))
  rw [show 0 + (n + 5) = n + 5 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 2, 0⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 4, 0, 0, n + 2, n⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨n + 4, (0 : ℕ), (0 : ℕ), n + 2, n⟩ [fm]⊢⁺
       ⟨(n + 1) + 4, (0 : ℕ), (0 : ℕ), (n + 1) + 2, n + 1⟩
  rw [show (n + 1) + 4 = n + 5 from by ring,
      show (n + 1) + 2 = n + 3 from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1327
