import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1491: [7/15, 9/14, 275/7, 4/55, 7/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  0
 0  0  2 -1  1
 2  0 -1  0 -1
-1  0  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1491

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R2+R5 drain: (2k, b, 0, 1, 0) -> (0, b+2k, 0, 1, 0)
theorem r2r5_drain : ∀ k b, ⟨2 * k, b, 0, 1, 0⟩ [fm]⊢* ⟨0, b + 2 * k, 0, 1, 0⟩ := by
  intro k; induction' k with k ih
  · intro b; exists 0
  · intro b
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 2)); ring_nf; finish

-- R3+R1+R1 interleaved chain: (0, 2k+1, 0, d+1, e) -> (0, 1, 0, d+k+1, e+k)
theorem r3r1r1_chain : ∀ k, ∀ d e, ⟨0, 2 * k + 1, 0, d + 1, e⟩ [fm]⊢* ⟨0, 1, 0, d + k + 1, e + k⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (d + 1) (e + 1)); ring_nf; finish

-- R3 chain: (0, 0, c, d+k, e) -> (0, 0, c+2k, d, e+k)
theorem r3_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e + k⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) d (e + 1)); ring_nf; finish

-- R4 chain: (a, 0, c+k, 0, e+k) -> (a+2k, 0, c, 0, e)
theorem r4_chain : ∀ k, ∀ a c e, ⟨a, 0, c + k, 0, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c e); ring_nf; finish

-- Main transition: (2*(n+1), 0, 1, 0, 0) ⊢⁺ (4*(n+1), 0, 1, 0, 0)
theorem main_trans (n : ℕ) :
    ⟨2 * (n + 1), 0, 1, 0, 0⟩ [fm]⊢⁺ ⟨4 * (n + 1), 0, 1, 0, 0⟩ := by
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (r2r5_drain n 1)
  rw [show 1 + 2 * n = 2 * n + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain n 0 0)
  rw [show 0 + n + 1 = (n + 1) from by ring,
      show (0 + n : ℕ) = n from by ring]
  step fm; step fm
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r3_chain (n + 1) 1 0 (0 + (n + 1)))
  rw [show 1 + 2 * (n + 1) = 1 + (2 * n + 2) from by ring,
      show 0 + (n + 1) + (n + 1) = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r4_chain (2 * n + 2) 0 1 0)
  rw [show 0 + 2 * (2 * n + 2) = 4 * (0 + (n + 1)) from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 1, 0, 0⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * (n + 1), 0, 1, 0, 0⟩) 0
  intro n
  exact ⟨2 * n + 1, by
    rw [show 2 * (2 * n + 1 + 1) = 4 * (n + 1) from by ring]
    exact main_trans n⟩

end Sz22_2003_unofficial_1491
