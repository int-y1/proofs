import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1031: [4/45, 5/14, 33/2, 63/11, 5/3]

Vector representation:
```
 2 -2 -1  0  0
-1  0  1 -1  0
-1  1  0  0  1
 0  2  0  1 -1
 0 -1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1031

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

theorem fm_r2 (a b d : ℕ) : fm ⟨a + 1, b, 0, d + 1, 0⟩ = some ⟨a, b, 1, d, 0⟩ := by
  unfold fm; rcases b with _ | _ | b <;> rfl

theorem r4_chain : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b, 0, d, k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm; apply stepStar_trans (ih (b + 2) (d + 1)); ring_nf; finish

theorem r3_chain : ∀ k, ∀ a b e,
    ⟨a + k, b, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; apply stepStar_trans (ih a (b + 1) (e + 1)); ring_nf; finish

theorem r1r2_chain : ∀ k, ∀ a b d,
    ⟨a, b + 2 * k, (1 : ℕ), d + k, 0⟩ [fm]⊢* ⟨a + k, b, 1, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · ring_nf; finish
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show a + (k + 1) = (a + 1) + k from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    apply stepStar_trans (step_stepStar (fm_r2 (a + 1) (b + 2 * k) (d + k)))
    apply stepStar_trans (ih (a + 1) b d); ring_nf; finish

theorem main_trans_base :
    ⟨(0 : ℕ), 8, 0, 3, 0⟩ [fm]⊢⁺ ⟨0, 14, 0, 5, 0⟩ := by
  execute fm 18

theorem main_trans_succ (n : ℕ) (hn : n ≥ 1) :
    ⟨(0 : ℕ), n * n + 5 * n + 8, 0, 2 * n + 3, 0⟩ [fm]⊢⁺
    ⟨0, n * n + 7 * n + 14, 0, 2 * n + 5, 0⟩ := by
  have h1 : ⟨(0 : ℕ), n * n + 5 * n + 8, 0, 2 * n + 3, 0⟩ [fm]⊢⁺
      ⟨0, n * n + 5 * n + 7, 1, 2 * n + 3, 0⟩ := by
    rw [show n * n + 5 * n + 8 = (n * n + 5 * n + 7) + 1 from by ring]
    step fm; finish
  have h2 : ⟨(0 : ℕ), n * n + 5 * n + 7, 1, 2 * n + 3, 0⟩ [fm]⊢*
      ⟨2 * n + 3, n * n + n + 1, 1, 0, 0⟩ := by
    have := r1r2_chain (2 * n + 3) 0 (n * n + n + 1) 0
    rw [show (n * n + n + 1) + 2 * (2 * n + 3) = n * n + 5 * n + 7 from by ring,
        show (0 : ℕ) + (2 * n + 3) = 2 * n + 3 from by ring] at this
    exact this
  have h3 : ⟨2 * n + 3, n * n + n + 1, (1 : ℕ), 0, 0⟩ [fm]⊢*
      ⟨2 * n + 5, n * n + n - 1, 0, 0, 0⟩ := by
    rw [show n * n + n + 1 = (n * n + n - 1) + 2 from by omega,
        show (1 : ℕ) = 0 + 1 from by ring]
    exact step_stepStar rfl
  have h4 : ⟨2 * n + 5, n * n + n - 1, (0 : ℕ), 0, 0⟩ [fm]⊢*
      ⟨0, n * n + 3 * n + 4, 0, 0, 2 * n + 5⟩ := by
    have := r3_chain (2 * n + 5) 0 (n * n + n - 1) 0
    simp only [Nat.zero_add] at this
    rw [show (n * n + n - 1) + (2 * n + 5) = n * n + 3 * n + 4 from by omega] at this
    exact this
  have h5 : ⟨(0 : ℕ), n * n + 3 * n + 4, 0, 0, 2 * n + 5⟩ [fm]⊢*
      ⟨0, n * n + 7 * n + 14, 0, 2 * n + 5, 0⟩ := by
    have := r4_chain (2 * n + 5) (n * n + 3 * n + 4) 0
    rw [show (n * n + 3 * n + 4) + 2 * (2 * n + 5) = n * n + 7 * n + 14 from by ring,
        show (0 : ℕ) + (2 * n + 5) = 2 * n + 5 from by ring] at this
    exact this
  exact stepPlus_stepStar_stepPlus h1
    (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), n * n + 5 * n + 8, 0, 2 * n + 3, 0⟩ [fm]⊢⁺
    ⟨0, (n + 1) * (n + 1) + 5 * (n + 1) + 8, 0, 2 * (n + 1) + 3, 0⟩ := by
  rw [show (n + 1) * (n + 1) + 5 * (n + 1) + 8 = n * n + 7 * n + 14 from by ring,
      show 2 * (n + 1) + 3 = 2 * n + 5 from by ring]
  rcases n with _ | n
  · exact main_trans_base
  · exact main_trans_succ (n + 1) (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 8, 0, 3, 0⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, n * n + 5 * n + 8, 0, 2 * n + 3, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
