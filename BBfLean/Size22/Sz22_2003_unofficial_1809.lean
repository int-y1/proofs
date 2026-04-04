import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1809: [9/10, 55/21, 2/3, 7/11, 297/2]

Vector representation:
```
-1  2 -1  0  0
 0 -1  1 -1  1
 1 -1  0  0  0
 0  0  0  1 -1
-1  3  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1809

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | _ => none

-- R2/R1 interleave: k rounds.
theorem r2r1_chain : ∀ k a b d e,
    ⟨a + k, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨a, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    rw [show (b + 2 : ℕ) = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih a (b + 1) d (e + 1))
    ring_nf; finish

-- R3 chain: move b to a.
theorem r3_chain : ∀ k a b e,
    ⟨a, b + k + 1, 0, 0, e⟩ [fm]⊢* ⟨a + k + 1, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · step fm; finish
  · rw [show b + (k + 1) + 1 = (b + k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b e)
    ring_nf; finish

-- R4 chain: move e to d.
theorem r4_chain : ∀ k a d e,
    ⟨a, 0, 0, d, e + k + 1⟩ [fm]⊢* ⟨a, 0, 0, d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · step fm; finish
  · rw [show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) e)
    ring_nf; finish

-- Compose all phases into a single ⊢* lemma.
theorem all_phases : ∀ n,
    ⟨2 * n, 3, 0, n, 1⟩ [fm]⊢* ⟨2 * n + 3, 0, 0, n + 1, 0⟩ := by
  intro n
  have h1 := r2r1_chain n n 2 0 1
  rw [show n + n = 2 * n from by ring, show (2 + 1 : ℕ) = 3 from by ring,
      show (0 + n : ℕ) = n from by ring] at h1
  apply stepStar_trans h1
  rw [show (2 + n + 1 : ℕ) = 0 + (n + 2) + 1 from by ring]
  apply stepStar_trans (r3_chain (n + 2) n 0 (1 + n))
  rw [show (1 + n : ℕ) = 0 + n + 1 from by ring]
  apply stepStar_trans (r4_chain n (n + (n + 2) + 1) 0 0)
  ring_nf; finish

-- Main transition: (2n+1, 0, 0, n, 0) →⁺ (2n+3, 0, 0, n+1, 0)
theorem main_trans : ∀ n, ⟨2 * n + 1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨2 * n + 3, 0, 0, n + 1, 0⟩ := by
  intro n
  rw [show 2 * n + 1 = 2 * n + 0 + 1 from by ring]
  step fm
  exact all_phases n

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 1, 0, 0, n, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1809
