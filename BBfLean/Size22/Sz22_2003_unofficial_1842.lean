import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1842: [9/20, 49/2, 44/21, 5/11, 3/7]

Vector representation:
```
-2  2 -1  0  0
-1  0  0  2  0
 2 -1  0 -1  1
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1842

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ c d e, ⟨(0 : ℕ), 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ b d e, ⟨(0 : ℕ), b + 1, k, d + k, e⟩ [fm]⊢* ⟨0, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b := b + 1) (d := d) (e := e + 1))
    ring_nf; finish

theorem drain : ∀ k, ∀ d e, ⟨(0 : ℕ), k, 0, d + 1, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    step fm
    step fm
    rw [show d + 2 + 2 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d + 3) (e + 1))
    ring_nf; finish

theorem phase1 : ∀ n, ⟨(0 : ℕ), 0, 0, 2 * n + 2, n⟩ [fm]⊢* ⟨0, 0, n, 2 * n + 2, 0⟩ := by
  intro n
  have h := e_to_c n 0 (2 * n + 2) 0
  simp only [Nat.zero_add] at h
  exact h

theorem phase2 : ∀ n, ⟨(0 : ℕ), 0, n, 2 * n + 2, 0⟩ [fm]⊢⁺ ⟨0, n + 1, 0, n + 1, n⟩ := by
  intro n
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  rw [show 2 * n + 1 = (n + 1) + n from by ring]
  apply stepStar_trans (r3r1_chain n 0 (n + 1) 0)
  ring_nf; finish

theorem phase3 : ∀ n, ⟨(0 : ℕ), n + 1, 0, n + 1, n⟩ [fm]⊢* ⟨0, 0, 0, 4 * n + 4, 2 * n + 1⟩ := by
  intro n
  rw [show n + (1 : ℕ) = n + 0 + 1 from by ring]
  apply stepStar_trans (drain (n + 1) n n)
  ring_nf; finish

theorem main_trans : ∀ n, ⟨(0 : ℕ), 0, 0, 2 * n + 2, n⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * n + 4, 2 * n + 1⟩ := by
  intro n
  apply stepStar_stepPlus_stepPlus (phase1 n)
  apply stepPlus_stepStar_stepPlus (phase2 n)
  exact phase3 n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 2, n⟩) 0
  intro n
  refine ⟨2 * n + 1, ?_⟩
  show ⟨(0 : ℕ), 0, 0, 2 * n + 2, n⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * (2 * n + 1) + 2, 2 * n + 1⟩
  rw [show 2 * (2 * n + 1) + 2 = 4 * n + 4 from by ring]
  exact main_trans n
