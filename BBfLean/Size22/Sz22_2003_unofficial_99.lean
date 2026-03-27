import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #99: [1/30, 35/3, 45/77, 2/7, 363/2]

Vector representation:
```
-1 -1 -1  0  0
 0 -1  1  1  0
 0  2  1 -1 -1
 1  0  0 -1  0
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_99

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a+k, 0, c, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + 1) + k from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

theorem r5r1_chain : ∀ n, ∀ c e, ⟨2*n+1, 0, c+n, 0, e⟩ [fm]⊢* ⟨0, 0, c+1, 1, e+2*n+2⟩ := by
  intro n; induction' n with n ih <;> intro c e
  · step fm; step fm; finish
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 from by ring,
      show c + (n + 1) = (c + n) + 1 from by ring]
  step fm
  rw [show (2 * n + 1 + 1 : ℕ) = (2 * n + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (ih c (e + 2))
  ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ c d, ⟨0, 0, c, d+1, k⟩ [fm]⊢* ⟨0, 0, c+3*k, d+k+1, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  step fm; step fm; step fm
  apply stepStar_trans (ih (c + 3) (d + 1))
  ring_nf; finish

theorem main_trans (c p : ℕ) :
    ⟨0, 0, c+p+1, 2*p+3, 0⟩ [fm]⊢⁺ ⟨0, 0, c+6*p+13, 2*p+5, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (r4_chain (2*p+3) 0 (c+p+1))
  simp only [Nat.zero_add]
  rw [show (2*p+3 : ℕ) = 2*(p+1)+1 from by ring,
      show c+p+1 = c + (p+1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (p+1) c 0)
  simp only [Nat.zero_add]
  rw [show (2 * (p + 1) + 2 : ℕ) = (2 * p + 3) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (r3r2r2_chain (2*p+3) (c+4) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 7, 3, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, p⟩ ↦ ⟨0, 0, c+p+1, 2*p+3, 0⟩) ⟨6, 0⟩
  intro ⟨c, p⟩
  refine ⟨⟨c+5*p+11, p+1⟩, ?_⟩
  show ⟨0, 0, c+p+1, 2*p+3, 0⟩ [fm]⊢⁺ ⟨0, 0, (c+5*p+11)+(p+1)+1, 2*(p+1)+3, 0⟩
  rw [show (c+5*p+11)+(p+1)+1 = c+6*p+13 from by ring,
      show 2*(p+1)+3 = 2*p+5 from by ring]
  exact main_trans c p

end Sz22_2003_unofficial_99
