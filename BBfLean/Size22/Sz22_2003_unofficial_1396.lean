import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1396: [7/15, 1/14, 99/7, 2/3, 5/22, 7/2]

Vector representation:
```
 0 -1 -1  1  0
-1  0  0 -1  0
 0  2  0 -1  1
 1 -1  0  0  0
-1  0  1  0 -1
-1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1396

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: (a, b+k, 0, 0, e) →* (a+k, b, 0, 0, e)
theorem r4_chain : ∀ k, ∀ a b e, (⟨a, b + k, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b e); ring_nf; finish

-- R5 chain: (a+k, 0, c, 0, k) →* (a, 0, c+k, 0, 0)
theorem r5_chain : ∀ k, ∀ a c, (⟨a + k, 0, c, 0, k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    step fm
    exact ih a (c + 1)

-- R3 chain: (0, b, 0, d+k, e) →* (0, b+2*k, 0, d, e+k)
theorem r3_chain : ∀ k, ∀ b d e, (⟨0, b, 0, d + k, e⟩ : Q) [fm]⊢* ⟨0, b + 2 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d (e + 1)); ring_nf; finish

-- Middle phase by strong induction on C.
-- (0, 2, C, d, e) →* (0, C+2*d+2, 0, 0, C+d+e) for C+d ≥ 1.
theorem middle_phase : ∀ C, ∀ d e, C + d ≥ 1 →
    (⟨0, 2, C, d, e⟩ : Q) [fm]⊢* ⟨0, C + 2 * d + 2, 0, 0, C + d + e⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro d e hcd
  rcases C with _ | _ | _ | C
  · -- C=0: R3 chain drains d (d ≥ 1)
    rw [show d = 0 + d from by ring]
    apply stepStar_trans (r3_chain d 2 0 e); ring_nf; finish
  · -- C=1: R1 then R3 chain
    step fm
    rw [show d + 1 = 0 + (d + 1) from by ring]
    apply stepStar_trans (r3_chain (d + 1) 1 0 e); ring_nf; finish
  · -- C=2: R1, R1, R3 chain
    step fm; step fm
    rw [show d + 2 = 0 + (d + 2) from by ring]
    apply stepStar_trans (r3_chain (d + 2) 0 0 e); ring_nf; finish
  · -- C+3: R1, R1, R3, then IH with C+1
    rw [show C + 3 = (C + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (C + 1) (by omega) (d + 1) (e + 1) (by omega))
    ring_nf; finish

-- Main transition: (0, n+2, 0, 0, n+1) →⁺ (0, n+3, 0, 0, n+2)
theorem main_trans (n : ℕ) :
    (⟨0, n + 2, 0, 0, n + 1⟩ : Q) [fm]⊢⁺ ⟨0, n + 3, 0, 0, n + 2⟩ := by
  -- Phase 1: R4 chain (n+2 steps)
  have h1 : (⟨0, n + 2, 0, 0, n + 1⟩ : Q) [fm]⊢* ⟨n + 2, 0, 0, 0, n + 1⟩ := by
    have := r4_chain (n + 2) 0 0 (n + 1)
    rw [show 0 + (n + 2) = n + 2 from by ring] at this; exact this
  -- Phase 2: R5 chain (n+1 steps)
  have h2 : (⟨n + 2, 0, 0, 0, n + 1⟩ : Q) [fm]⊢* ⟨1, 0, n + 1, 0, 0⟩ := by
    have := r5_chain (n + 1) 1 0
    rw [show 1 + (n + 1) = n + 2 from by ring,
        show 0 + (n + 1) = n + 1 from by ring] at this; exact this
  -- Phase 3: R6 then R3 (2 steps)
  have h3 : (⟨1, 0, n + 1, 0, 0⟩ : Q) [fm]⊢⁺ ⟨0, 2, n + 1, 0, 1⟩ := by
    rw [show n + 1 = (n + 1) from rfl]; step fm; step fm; finish
  -- Phase 4: Middle phase
  have h4 : (⟨0, 2, n + 1, 0, 1⟩ : Q) [fm]⊢* ⟨0, n + 3, 0, 0, n + 2⟩ := by
    have := middle_phase (n + 1) 0 1 (by omega)
    rw [show (n + 1) + 2 * 0 + 2 = n + 3 from by ring,
        show (n + 1) + 0 + 1 = n + 2 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepStar_stepPlus_stepPlus h2
      (stepPlus_stepStar_stepPlus h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, n + 2, 0, 0, n + 1⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1396
