import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1794: [9/10, 49/2, 22/21, 5/121, 9/7]

Vector representation:
```
-1  2 -1  0  0
-1  0  0  2  0
 1 -1  0 -1  1
 0  0  1  0 -2
 0  2  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1794

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d, 2*k) →* (0, 0, c+k, d, 0)
theorem e_to_c : ∀ k, ∀ c d, ⟨(0 : ℕ), 0, c, d, 2 * k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R3+R1 chain: (0, b+1, k, k+1, e) →* (0, b+k+1, 0, 1, e+k)
theorem r3r1_chain : ∀ k, ∀ b e, ⟨(0 : ℕ), b + 1, k, k + 1, e⟩ [fm]⊢* ⟨0, b + k + 1, 0, 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show (k + 1 : ℕ) + 1 = k + 1 + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (b + 1) (e + 1))
    ring_nf; finish

-- R3+R2 chain: (0, k, 0, d+1, e) →* (0, 0, 0, d+k+1, e+k)
theorem r3r2_chain : ∀ k, ∀ d e, ⟨(0 : ℕ), k, 0, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

-- (0, 0, 0, n+2, 2*n) →⁺ (0, 0, 0, n+3, 2*n+2)
theorem main_trans : ⟨(0 : ℕ), 0, 0, n + 2, 2 * n⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 3, 2 * n + 2⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_c n 0 (n + 2))
  show ⟨(0 : ℕ), 0, 0 + n, n + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 3, 2 * n + 2⟩
  rw [show n + 2 = (n + 1) + 1 from by ring]
  step fm
  show ⟨(0 : ℕ), 2, 0 + n, n + 1, 0⟩ [fm]⊢* ⟨0, 0, 0, n + 3, 2 * n + 2⟩
  rw [show (0 : ℕ) + n = n from by omega]
  apply stepStar_trans (r3r1_chain n 1 0)
  show ⟨(0 : ℕ), 1 + n + 1, 0, 1, 0 + n⟩ [fm]⊢* ⟨0, 0, 0, n + 3, 2 * n + 2⟩
  rw [show 1 + n + 1 = n + 2 from by omega,
      show (0 : ℕ) + n = n from by omega]
  apply stepStar_trans (r3r2_chain (n + 2) 0 n)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n + 2, 2 * n⟩) 0
  intro n; exists n + 1
  show ⟨(0 : ℕ), 0, 0, n + 2, 2 * n⟩ [fm]⊢⁺ ⟨0, 0, 0, (n + 1) + 2, 2 * (n + 1)⟩
  rw [show (n + 1) + 2 = n + 3 from by ring,
      show 2 * (n + 1) = 2 * n + 2 from by ring]
  exact main_trans
