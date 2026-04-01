import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1301: [63/10, 121/2, 2/33, 5/7, 63/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 1 -1  0  0 -1
 0  0  1 -1  0
 0  2  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1301

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R4 repeated: move d to c
theorem d_to_c : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (c + 1) d e); ring_nf; finish

-- R1+R3 chain
theorem r1r3_chain : ∀ k, ∀ b c d e, ⟨(1 : ℕ), b, c + k, d, e + k⟩ [fm]⊢* ⟨(1 : ℕ), b + k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) c (d + 1) e); ring_nf; finish

-- R3+R2 chain
theorem r3r2_chain : ∀ k, ∀ d e, ⟨(0 : ℕ), k, (0 : ℕ), d, e + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]; step fm; step fm
    apply stepStar_trans (ih d (e + 1)); ring_nf; finish

-- Main transition: (0, 0, 0, n, n+2) →⁺ (0, 0, 0, n+1, n+3)
theorem main_transition (n : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), 0, n, n + 2⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 0, n + 1, n + 3⟩ := by
  -- Phase 1: d_to_c
  have h1 : ⟨(0 : ℕ), (0 : ℕ), 0, 0 + n, n + 2⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), 0 + n, 0, n + 2⟩ :=
    d_to_c n 0 0 (n + 2)
  rw [show (0 : ℕ) + n = n from by ring] at h1
  -- Phase 2: opening R5+R3
  have h2 : ⟨(0 : ℕ), (0 : ℕ), n, 0, n + 2⟩ [fm]⊢⁺ ⟨(1 : ℕ), 1, n, 1, n⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring]; step fm; step fm; finish
  -- Phase 3: R1+R3 chain
  have h3 : ⟨(1 : ℕ), 1, 0 + n, 1, 0 + n⟩ [fm]⊢* ⟨(1 : ℕ), 1 + n, 0, 1 + n, 0⟩ :=
    r1r3_chain n 1 0 1 0
  rw [show (0 : ℕ) + n = n from by ring, show (1 : ℕ) + n = n + 1 from by ring] at h3
  -- Phase 4: R2
  have h4 : (⟨1, n + 1, 0, n + 1, 0⟩ : Q) [fm]⊢ ⟨0, n + 1, 0, n + 1, 2⟩ := by simp [fm]
  -- Phase 5: R3+R2 chain
  have h5 : ⟨(0 : ℕ), n + 1, (0 : ℕ), n + 1, 1 + 1⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), n + 1, 1 + (n + 1) + 1⟩ :=
    r3r2_chain (n + 1) (n + 1) 1
  rw [show (1 : ℕ) + 1 = 2 from by ring, show 1 + (n + 1) + 1 = n + 3 from by ring] at h5
  -- Compose
  apply stepStar_stepPlus_stepPlus h1
  apply stepPlus_stepStar_stepPlus h2
  apply stepStar_trans h3
  apply stepStar_trans (step_stepStar h4)
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n, n + 2⟩) 0
  intro n
  exists n + 1
  exact main_transition n

end Sz22_2003_unofficial_1301
