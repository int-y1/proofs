import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1966: [99/35, 11/6, 5/3, 2/55, 147/2]

Vector representation:
```
 0  2 -1 -1  1
-1 -1  0  0  1
 0 -1  1  0  0
 1  0 -1  0 -1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1966

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R1+R3 interleaving: (0, k, 1, D+1, E) →* (0, k+D+2, 0, 0, E+D+1)
theorem r1r3_interleave : ∀ D, ⟨(0 : ℕ), k, 1, D + 1, E⟩ [fm]⊢* ⟨0, k + D + 2, 0, 0, E + D + 1⟩ := by
  intro D; induction' D with D ih generalizing k E
  · step fm; ring_nf; finish
  · rw [show D + 1 + 1 = (D + 1) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (k := k + 1) (E := E + 1))
    ring_nf; finish

-- Drain b to c: (0, b, c, 0, e) →* (0, 0, b+c, 0, e)
theorem b_to_c : ∀ b, ∀ c, ⟨(0 : ℕ), b, c, 0, e⟩ [fm]⊢* ⟨0, 0, b + c, 0, e⟩ := by
  intro b; induction' b with b ih <;> intro c
  · ring_nf; finish
  · step fm
    apply stepStar_trans (ih (c + 1))
    ring_nf; finish

-- R4 chain: (a, 0, k+1, 0, e+k+1) →* (a+k+1, 0, 0, 0, e)
theorem r4_chain : ∀ k, ∀ a e, ⟨a, 0, k + 1, 0, e + k + 1⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; ring_nf; finish
  · rw [show e + (k + 1) + 1 = (e + 1) + k + 1 from by ring]
    step fm
    rw [show e + 1 + k = e + k + 1 from by ring]
    apply stepStar_trans (ih (a + 1) e)
    ring_nf; finish

-- R5+R2 drain: (2*a+1, 0, 0, D, e) →* (1, 0, 0, D+2*a, e+a)
theorem r5r2_drain : ∀ a, ∀ D e, ⟨2 * a + 1, 0, 0, D, e⟩ [fm]⊢* ⟨1, 0, 0, D + 2 * a, e + a⟩ := by
  intro a; induction' a with a ih <;> intro D e
  · ring_nf; finish
  · rw [show 2 * (a + 1) + 1 = (2 * a + 1) + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (D + 2) (e + 1))
    ring_nf; finish

-- Main transition: (1, 0, 0, 2*n+2, E+1) ⊢⁺ (1, 0, 0, 2*n+4, E+n+2)
theorem main_trans : ⟨1, 0, 0, 2 * n + 2, E + 1⟩ [fm]⊢⁺ ⟨1, 0, 0, 2 * n + 4, E + n + 2⟩ := by
  step fm
  step fm
  rw [show 2 * n + 2 + 2 = (2 * n + 3) + 1 from by ring]
  apply stepStar_trans (r1r3_interleave (2 * n + 3) (k := 0) (E := E + 1))
  rw [show 0 + (2 * n + 3) + 2 = 2 * n + 5 from by ring,
      show E + 1 + (2 * n + 3) + 1 = E + (2 * n + 5) from by ring]
  apply stepStar_trans (b_to_c (2 * n + 5) 0 (e := E + (2 * n + 5)))
  rw [show (2 * n + 5 : ℕ) + 0 = (2 * n + 4) + 1 from by ring,
      show E + (2 * n + 5) = E + (2 * n + 4) + 1 from by ring]
  apply stepStar_trans (r4_chain (2 * n + 4) 0 E)
  rw [show 0 + (2 * n + 4) + 1 = 2 * (n + 2) + 1 from by ring]
  apply stepStar_trans (r5r2_drain (n + 2) 0 E)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 1⟩) (by execute fm 23)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, E⟩ ↦ ⟨1, 0, 0, 2 * n + 2, E + 1⟩) ⟨0, 0⟩
  intro ⟨n, E⟩; exact ⟨⟨n + 1, E + n + 1⟩, main_trans⟩

end Sz22_2003_unofficial_1966
