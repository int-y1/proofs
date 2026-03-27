import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #584: [35/6, 11/2, 8/55, 3/7, 12/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 3  0 -1  0 -1
 0  1  0 -1  0
 2  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_584

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: d → b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _); ring_nf; finish

-- R3+R2x3 chain: (0, 0, c+k, D, e+1) →* (0, 0, c, D, e+1+2*k)
theorem r3r2_chain : ∀ k c (D : ℕ) e,
    ⟨0, 0, c + k, D, e + 1⟩ [fm]⊢* ⟨0, 0, c, D, e + 1 + 2 * k⟩ := by
  intro k; induction' k with k h <;> intro c D e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show e + 1 + 1 + 1 = (e + 2) + 1 from by ring]
  apply stepStar_trans (h c D (e + 2)); ring_nf; finish

-- Combined interleave + drain by strong induction on B.
-- From (0, B, C+1, D, f+B+1) reach (0, 0, 0, D+B, f+2*C+2*B+3)
theorem interleave_drain :
    ∀ B, ∀ C D f,
    ⟨0, B, C + 1, D, f + B + 1⟩ [fm]⊢* ⟨0, 0, 0, D + B, f + 2 * C + 2 * B + 3⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro C D f
  rcases B with _ | _ | _ | B
  · -- B = 0: R3/R2 chain (C+1 rounds)
    -- State: (0, 0, C+1, D, f+1). Apply r3r2_chain with k=C+1, c=0, e=f.
    rw [show C + 1 = 0 + (C + 1) from by ring]
    apply stepStar_trans (r3r2_chain (C + 1) 0 D f)
    ring_nf; finish
  · -- B = 1: R3, R1, R2, R2 then R3/R2 chain
    -- State: (0, 1, C+1, D, f+2)
    rw [show f + 1 + 1 = (f + 1) + 1 from by ring]
    step fm; step fm; step fm; step fm
    -- Now at (0, 0, C+1, D+1, f+3). Apply r3r2_chain with k=C+1, c=0, e=f+2.
    rw [show C + 1 = 0 + (C + 1) from by ring,
        show f + 1 + 1 + 1 = (f + 2) + 1 from by ring]
    apply stepStar_trans (r3r2_chain (C + 1) 0 (D + 1) (f + 2))
    ring_nf; finish
  · -- B = 2: R3, R1, R1, R2 then R3/R2 chain
    -- State: (0, 2, C+1, D, f+3)
    rw [show f + 2 + 1 = (f + 2) + 1 from by ring]
    step fm; step fm; step fm; step fm
    -- Now at (0, 0, C+2, D+2, f+3). Apply r3r2_chain with k=C+2, c=0, e=f+2.
    rw [show C + 1 + 1 = 0 + (C + 2) from by ring,
        show f + 2 + 1 = (f + 2) + 1 from by ring]
    apply stepStar_trans (r3r2_chain (C + 2) 0 (D + 2) (f + 2))
    ring_nf; finish
  · -- B+3: R3, R1, R1, R1 then recurse
    -- State: (0, B+3, C+1, D, f+B+4)
    rw [show f + (B + 3) + 1 = (f + B + 3) + 1 from by ring]
    step fm; step fm; step fm; step fm
    -- Now at (0, B, C+3, D+3, f+B+3).
    rw [show C + 1 + 1 + 1 = (C + 2) + 1 from by ring,
        show f + B + 3 = (f + 2) + B + 1 from by ring]
    apply stepStar_trans (ih B (by omega) (C + 2) (D + 3) (f + 2))
    ring_nf; finish

-- Main transition: (0, 0, 0, n+1, e+n+2) ⊢⁺ (0, 0, 0, n+2, e+2*n+5)
theorem main_trans : ⟨0, 0, 0, n + 1, e + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, e + 2 * n + 5⟩ := by
  -- Phase 1: d_to_b: (0,0,0,n+1,e+n+2) →* (0,n+1,0,0,e+n+2)
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (n + 1) 0)
  rw [show 0 + (n + 1) = n + 1 from by ring]
  -- Phase 2: R5, R1, R1: (0,n+1,0,0,e+n+2) → (0,n,2,2,e+n+1)
  rw [show e + n + 2 = (e + n + 1) + 1 from by ring]
  step fm
  rw [show n + 1 + 1 = (n + 1) + 1 from by ring]
  step fm; step fm
  -- Phase 3: interleave_drain: (0, n, 1+1, 2, e+n+1)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show e + n + 1 = e + n + 1 from rfl]
  apply stepStar_trans (interleave_drain n 1 2 e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 0, 0, n + 1, e + n + 2⟩) ⟨0, 1⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + 1, e + n + 2⟩, ?_⟩
  show ⟨0, 0, 0, n + 1, e + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, (n + 1) + 1, (e + n + 2) + (n + 1) + 2⟩
  rw [show (n + 1) + 1 = n + 2 from by ring,
      show (e + n + 2) + (n + 1) + 2 = e + 2 * n + 5 from by ring]
  exact main_trans

end Sz22_2003_unofficial_584
