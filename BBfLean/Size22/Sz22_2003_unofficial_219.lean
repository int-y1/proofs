import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #219: [10/3, 33/35, 1/5, 343/2, 1/77, 5/7]

Vector representation:
```
 1 -1  1  0  0
 0  1 -1 -1  1
 0  0 -1  0  0
-1  0  0  3  0
 0  0  0 -1 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_219

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R1+R2 loop: (a, 1, 0, K, e) →* (a+K, 1, 0, 0, e+K)
theorem r1r2_loop : ∀ K, ∀ a e, ⟨a, 1, 0, K, e⟩ [fm]⊢* ⟨a+K, 1, 0, 0, e+K⟩ := by
  intro K; induction' K with K ih <;> intro a e
  · exists 0
  step fm; step fm
  apply stepStar_trans (ih (a+1) (e+1))
  ring_nf; finish

-- R4 chain: (A, 0, 0, D, E) →* (0, 0, 0, D+3*A, E)
theorem r4_chain : ∀ A, ∀ D E, ⟨A, 0, 0, D, E⟩ [fm]⊢* ⟨0, 0, 0, D+3*A, E⟩ := by
  intro A; induction' A with A ih <;> intro D E
  · exists 0
  step fm
  apply stepStar_trans (ih (D+3) E)
  ring_nf; finish

-- R5 chain: (0, 0, 0, D+K, K) →* (0, 0, 0, D, 0)
theorem r5_chain : ∀ K, ∀ D, ⟨0, 0, 0, D+K, K⟩ [fm]⊢* ⟨0, 0, 0, D, 0⟩ := by
  intro K; induction' K with K ih <;> intro D
  · exists 0
  rw [show D + (K + 1) = (D + K) + 1 from by ring]
  step fm
  exact ih D

-- Full cycle: (0, 0, 0, D+3, 0) →* (0, 0, 0, 2*D+4, 0)
theorem full_cycle (D : ℕ) : ⟨0, 0, 0, D+3, 0⟩ [fm]⊢* ⟨0, 0, 0, 2*D+4, 0⟩ := by
  -- R6: (0,0,0,(D+2)+1,0) → (0,0,1,D+2,0)
  rw [show D + 3 = (D + 2) + 1 from by ring]
  step fm
  -- R2: (0,0,0+1,(D+1)+1,0) → (0,1,0,D+1,1)
  rw [show D + 2 = (D + 1) + 1 from by ring]
  step fm
  -- R1+R2 loop D+1 times
  apply stepStar_trans (r1r2_loop (D+1) 0 1)
  simp only [Nat.zero_add]
  rw [show 1 + (D + 1) = D + 2 from by ring]
  -- R1: (D+1, 1, 0, 0, D+2) → (D+2, 0, 1, 0, D+2)
  step fm
  -- R3: (D+2, 0, 1, 0, D+2) → (D+2, 0, 0, 0, D+2)
  step fm
  -- R4 chain
  apply stepStar_trans (r4_chain (D+2) 0 (D+2))
  simp only [Nat.zero_add]
  -- R5 chain
  rw [show 3 * (D + 2) = (2 * D + 4) + (D + 2) from by ring]
  exact r5_chain (D+2) (2*D+4)

-- Promote full_cycle to stepPlus
theorem main_trans (D : ℕ) : ⟨0, 0, 0, D+3, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*D+4, 0⟩ :=
  stepStar_stepPlus (full_cycle D) (by
    intro heq
    have h := congr_arg (fun q : Q => q.2.2.2.1) heq
    simp only at h
    omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun D ↦ ⟨0, 0, 0, D+3, 0⟩) 0
  intro D; exact ⟨2*D+1, by
    show ⟨0, 0, 0, D+3, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, (2*D+1)+3, 0⟩
    rw [show (2 * D + 1) + 3 = 2 * D + 4 from by ring]
    exact main_trans D⟩

end Sz22_2003_unofficial_219
