import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #940: [4/15, 33/14, 25/2, 7/11, 66/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_940

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b+1, c, d, e+1⟩
  | _ => none

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e + 1⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e); ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem main_trans (n c : ℕ) :
    ⟨0, 0, c + n + 2, n, 0⟩ [fm]⊢⁺ ⟨0, 0, c + 2 * n + 6, n + 1, 0⟩ := by
  -- R5: (0, 0, c+n+2, n, 0) -> (1, 1, c+n+1, n, 1)
  rw [show c + n + 2 = (c + n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (c + n + 1) + 1, n, 0⟩ = some ⟨1, 1, c + n + 1, n, 1⟩
    unfold fm; simp only
  -- R1: (1, 1, c+n+1, n, 1) -> (3, 0, c+n, n, 1)
  rw [show c + n + 1 = (c + n) + 1 from by ring]
  have h1 : ⟨(1 : ℕ), 1, (c + n) + 1, n, 1⟩ [fm]⊢* ⟨3, 0, c + n, n, 1⟩ := by
    step fm; finish
  apply stepStar_trans h1
  -- R2/R1 chain: (3, 0, c+n, n, 1) -> (n+3, 0, c, 0, n+1)
  have h2 : ⟨3, 0, c + n, n, 1⟩ [fm]⊢* ⟨n + 3, 0, c, 0, n + 1⟩ := by
    have := r2r1_chain n 2 c 0
    rw [show 2 + n + 1 = n + 3 from by ring,
        show 0 + n + 1 = n + 1 from by ring,
        show 2 + 1 = 3 from by ring] at this
    exact this
  apply stepStar_trans h2
  -- R3 drain: (n+3, 0, c, 0, n+1) -> (0, 0, c+2*(n+3), 0, n+1)
  have h3 : ⟨n + 3, 0, c, 0, n + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * (n + 3), 0, n + 1⟩ :=
    r3_drain (n + 3) c (n + 1)
  apply stepStar_trans h3
  -- R4 drain: (0, 0, c+2*(n+3), 0, n+1) -> (0, 0, c+2*(n+3), n+1, 0)
  have h4 : ⟨0, 0, c + 2 * (n + 3), 0, n + 1⟩ [fm]⊢* ⟨0, 0, c + 2 * (n + 3), n + 1, 0⟩ := by
    have := r4_drain (n + 1) (c + 2 * (n + 3)) 0
    rw [show 0 + (n + 1) = n + 1 from by ring] at this
    exact this
  apply stepStar_trans h4
  rw [show c + 2 * (n + 3) = c + 2 * n + 6 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, c⟩ ↦ ⟨0, 0, c + n + 2, n, 0⟩) ⟨0, 0⟩
  intro ⟨n, c⟩
  refine ⟨⟨n + 1, c + n + 3⟩, ?_⟩
  show ⟨0, 0, c + n + 2, n, 0⟩ [fm]⊢⁺ ⟨0, 0, (c + n + 3) + (n + 1) + 2, n + 1, 0⟩
  rw [show (c + n + 3) + (n + 1) + 2 = c + 2 * n + 6 from by ring]
  exact main_trans n c

end Sz22_2003_unofficial_940
