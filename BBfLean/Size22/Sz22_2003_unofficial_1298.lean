import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1298: [63/10, 121/2, 2/33, 5/7, 28/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 1 -1  0  0 -1
 0  0  1 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1298

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer d to c
theorem d_to_c : ∀ k c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 1) d); ring_nf; finish

-- R3+R1 chain: interleaved consumption of c
theorem r3r1_chain : ∀ k b c d e, ⟨0, b + 1, c + k, d, e + k⟩ [fm]⊢* ⟨0, b + k + 1, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e); ring_nf; finish

-- R3+R2 drain: b to e
theorem r3r2_drain : ∀ k d e, ⟨0, k, 0, d, e + k⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show e + k + 2 = (e + 2) + k from by ring]
    apply stepStar_trans (ih d (e + 2))
    rw [show e + 2 + 2 * k = e + 2 * (k + 1) from by ring]; finish

-- Main transition: (0,0,0,n+2,3n+8) ⊢⁺ (0,0,0,n+3,3n+11)
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n + 2, 3 * n + 8⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 3, 3 * n + 11⟩ := by
  -- Phase 1: d_to_c: (0,0,0,n+2,3n+8) -> (0,0,n+2,0,3n+8)
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (n + 2) 0 0 (e := 3 * n + 8))
  rw [show 0 + (n + 2) = n + 2 from by ring]
  -- Phase 2: R5: (0,0,n+2,0,3n+8) -> (2,0,n+2,1,3n+7)
  rw [show 3 * n + 8 = (3 * n + 7) + 1 from by ring]
  step fm
  -- Phase 3: 2 R1 steps: (2,0,n+2,1,3n+7) -> (0,4,n,3,3n+7)
  rw [show n + 2 = n + 1 + 1 from by ring]; step fm
  rw [show n + 1 = (0 + n) + 1 from by ring]; step fm
  -- Phase 4: R3+R1 chain (n rounds): (0,4,n,3,3n+7) -> (0,n+4,0,n+3,2n+7)
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 3 * n + 7 = (2 * n + 7) + n from by ring]
  apply stepStar_trans (r3r1_chain n 3 0 3 (2 * n + 7))
  rw [show 3 + n + 1 = n + 4 from by ring,
      show 3 + n = n + 3 from by ring]
  -- Phase 5: R3+R2 drain (n+4 rounds): (0,n+4,0,n+3,2n+7) -> (0,0,0,n+3,3n+11)
  rw [show 2 * n + 7 = (n + 3) + (n + 4) from by ring]
  apply stepStar_trans (r3r2_drain (n + 4) (n + 3) (n + 3))
  rw [show n + 3 + 2 * (n + 4) = 3 * n + 11 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 8⟩)
  · execute fm 12
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 3 * n + 8⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1298
