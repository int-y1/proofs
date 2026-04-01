import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1296: [63/10, 121/2, 2/33, 5/7, 14/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 1 -1  0  0 -1
 0  0  1 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1296

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Transfer d to c via R4.
theorem d_to_c : ∀ k c d, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (c + 1) d); ring_nf; finish

-- R3+R1 chain: (0, b, c+k, d, e+k) ⊢* (0, b+k, c, d+k, e).
-- Each R3+R1 pair: b+1, c-1, d+1, e-1.
theorem r3r1_chain : ∀ k, ∀ b c d e, ⟨0, b + 1, c + k, d, e + k⟩ [fm]⊢* ⟨0, b + k + 1, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e); ring_nf; finish

-- R3+R2 chain: (0, k, 0, d, e+1) ⊢* (0, 0, 0, d, e+k+1).
-- Each R3+R2 pair: b-1, e+1 (net).
theorem r3r2_chain : ∀ k, ∀ d e, ⟨0, k, 0, d, e + 1⟩ [fm]⊢* ⟨0, 0, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih d (e + 1)); ring_nf; finish

-- Main transition: (0, 0, 0, n+2, n+4) ⊢⁺ (0, 0, 0, n+3, n+5).
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n + 2, n + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 3, n + 5⟩ := by
  -- Phase 1: d_to_c: (0,0,0,n+2,n+4) -> (0,0,n+2,0,n+4)
  rw [show (n + 2 : ℕ) = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (n + 2) 0 0 (e := n + 4))
  rw [show 0 + (n + 2) = n + 2 from by ring]
  -- Phase 2: R5: (0,0,n+2,0,(n+3)+1) -> (1,0,n+2,1,n+3)
  rw [show (n + 4 : ℕ) = (n + 3) + 1 from by ring]
  step fm
  -- Phase 3: R1: (1,0,(n+1)+1,1,n+3) -> (0,2,n+1,2,n+3)
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  -- Now at: (0, 2, n+1, 2, n+3)
  -- Phase 4: R3+R1 chain with k=n+1, b=1, c=0, d=2, e=2:
  -- Need: (0, 1+1, 0+(n+1), 2, 2+(n+1)) ⊢* (0, 1+(n+1)+1, 0, 2+(n+1), 2)
  rw [show (n + 1 : ℕ) = 0 + (n + 1) from by ring,
      show (n + 3 : ℕ) = 2 + (n + 1) from by ring]
  apply stepStar_trans (r3r1_chain (n + 1) 1 0 2 2)
  rw [show 1 + (n + 1) + 1 = n + 3 from by ring,
      show 2 + (n + 1) = n + 3 from by ring]
  -- Now at: (0, n+3, 0, n+3, 2)
  -- Phase 5: R3+R2 chain with k=n+3, d=n+3, e=1:
  -- (0, n+3, 0, n+3, 1+1) ⊢* (0, 0, 0, n+3, 1+(n+3)+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (n + 3) (n + 3) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 4⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, n + 4⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1296
