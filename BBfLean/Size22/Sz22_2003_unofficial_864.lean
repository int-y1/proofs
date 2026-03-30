import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #864: [4/105, 15/22, 21/2, 11/3, 4/7]

Vector representation:
```
 2 -1 -1 -1  0
-1  1  1  0 -1
-1  1  0  1  0
 0 -1  0  0  1
 2  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_864

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- R4 repeated: move b to e.
theorem b_to_e : ∀ k b d e, ⟨(0 : ℕ), b + k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih b d (e + 1)); exists 0; ring_nf; rfl

-- R2+R1 chain.
theorem r2r1_chain : ∀ k a e, ⟨a + 2, 0, 0, k, e + 1 + k⟩ [fm]⊢* ⟨a + k + 2, 0, 0, 0, e + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show e + 1 + (k + 1) = (e + 1 + k) + 1 from by ring]
    step fm; step fm
    show ⟨(a + 1) + 2, 0, 0, k, e + 1 + k⟩ [fm]⊢* _
    apply stepStar_trans (ih (a + 1) e); exists 0; ring_nf; rfl

-- R2 repeated.
theorem r2_chain : ∀ k a b c, ⟨a + 1 + k, b, c, 0, k⟩ [fm]⊢* ⟨a + 1, b + k, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show a + 1 + (k + 1) = (a + 1 + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (b + 1) (c + 1)); exists 0; ring_nf; rfl

-- R3+R1 interleaved.
theorem r3r1_chain : ∀ k a b, ⟨a + 1, b + 1, k, 0, 0⟩ [fm]⊢* ⟨a + 1 + k, b + 1, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  · step fm; step fm
    show ⟨(a + 1) + 1, b + 1, k, 0, 0⟩ [fm]⊢* _
    apply stepStar_trans (ih (a + 1) b); exists 0; ring_nf; rfl

-- R3 repeated.
theorem r3_chain : ∀ k a b d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b + k, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (b + 1) (d + 1)); exists 0; ring_nf; rfl

-- Full cycle
theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 2 * n + 3, 0, n + 2, 0⟩ [fm]⊢⁺ ⟨0, 2 * n + 5, 0, n + 3, 0⟩ := by
  have h1 : ⟨(0 : ℕ), 2 * n + 3, 0, n + 2, 0⟩ [fm]⊢* ⟨0, 0, 0, n + 2, 2 * n + 3⟩ := by
    convert b_to_e (2 * n + 3) 0 (n + 2) 0 using 2; all_goals ring_nf
  have h2 : ⟨(0 : ℕ), 0, 0, n + 2, 2 * n + 3⟩ [fm]⊢ ⟨2, 0, 0, n + 1, 2 * n + 3⟩ := by
    rw [show n + 2 = (n + 1) + 1 from by ring,
        show 2 * n + 3 = 2 * n + 2 + 1 from by ring]
    show fm (0, 0, 0, (n + 1) + 1, 2 * n + 2 + 1) = some (2, 0, 0, n + 1, 2 * n + 2 + 1)
    unfold fm; rfl
  have h3 : ⟨(2 : ℕ), 0, 0, n + 1, 2 * n + 3⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, n + 2⟩ := by
    convert r2r1_chain (n + 1) 0 (n + 1) using 2; all_goals ring_nf
  have h4 : ⟨n + 3, 0, 0, 0, n + 2⟩ [fm]⊢* ⟨(1 : ℕ), n + 2, n + 2, 0, 0⟩ := by
    convert r2_chain (n + 2) 0 0 0 using 2; all_goals ring_nf
  have h5 : ⟨(1 : ℕ), n + 2, n + 2, 0, 0⟩ [fm]⊢* ⟨n + 3, n + 2, 0, 0, 0⟩ := by
    convert r3r1_chain (n + 2) 0 (n + 1) using 2; all_goals ring_nf
  have h6 : ⟨n + 3, n + 2, 0, 0, 0⟩ [fm]⊢* ⟨(0 : ℕ), 2 * n + 5, 0, n + 3, 0⟩ := by
    convert r3_chain (n + 3) 0 (n + 2) 0 using 2; all_goals ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2
      (stepStar_trans (stepStar_trans (stepStar_trans h3 h4) h5) h6))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 3, 0, 2, 0⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2 * n + 3, 0, n + 2, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
