import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1084: [5/6, 2/35, 3773/2, 3/49, 10/11]

Vector representation:
```
-1 -1  1  0  0
 1  0 -1 -1  0
-1  0  0  3  1
 0  1  0 -2  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1084

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e+1⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

private theorem r3_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + 3 * (k + 1) = (d + 3) + 3 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    step fm; exact ih (d + 3) (e + 1)

private theorem r4_drain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 0, d + 2 * k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · ring_nf; finish
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d e

private theorem r2_chain : ∀ k, ∀ a c d e,
    ⟨a, (0 : ℕ), c + k, d + k, e⟩ [fm]⊢* ⟨a + k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring,
        show a + (k + 1) = (a + 1) + k from by ring]
    step fm; exact ih (a + 1) c d e

private theorem r1_r5_chain : ∀ k, ∀ c,
    ⟨(1 : ℕ), k, c, 0, k⟩ [fm]⊢* ⟨1, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · ring_nf; finish
  · rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    step fm; step fm; exact ih (c + 2)

private theorem second_half : ∀ c, ∀ a e,
    ⟨a + 1, (0 : ℕ), c, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 3 * (a + 1), e + c + a + 1⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih
  rcases c with _ | _ | _ | c
  · -- c = 0
    intro a e
    have h := r3_drain (a + 1) 0 e
    simp only [Nat.zero_add] at h
    convert h using 1; ring_nf
  · -- c = 1
    intro a e
    step fm; step fm
    have h := r3_drain (a + 1) 2 (e + 1)
    convert h using 1
  · -- c = 2
    intro a e
    step fm; step fm; step fm
    have h := r3_drain (a + 2) 1 (e + 1)
    convert h using 1; ring_nf
  · -- c + 3
    intro a e
    step fm
    have h1 := r2_chain 3 a c 0 (e + 1)
    simp only [Nat.zero_add] at h1
    have h2 := ih c (by omega) (a + 2) (e + 1)
    rw [show a + 3 = (a + 2) + 1 from by ring] at h1
    apply stepStar_trans h1
    convert h2 using 1; ring_nf

private theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * n + 3, n + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * n + 5, 2 * n + 2⟩ := by
  have h1 : ⟨(0 : ℕ), 0, 0, 2 * n + 3, n + 1⟩ [fm]⊢* ⟨0, n + 1, 0, 1, n + 1⟩ := by
    have h := r4_drain (n + 1) 0 1 (n + 1)
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * (n + 1) = 2 * n + 3 from by ring] at h
    exact h
  have h2 : ⟨(0 : ℕ), n + 1, 0, 1, n + 1⟩ [fm]⊢⁺ ⟨1, n, 1, 0, n⟩ := by
    rw [show n + 1 = n + 1 from rfl]
    step fm; step fm; step fm; ring_nf; finish
  have h3 : ⟨(1 : ℕ), n, 1, 0, n⟩ [fm]⊢* ⟨1, 0, 2 * n + 1, 0, 0⟩ := by
    have h := r1_r5_chain n 1
    convert h using 1; ring_nf
  have h4 : ⟨(1 : ℕ), 0, 2 * n + 1, 0, 0⟩ [fm]⊢* ⟨0, 0, 0, 4 * n + 5, 2 * n + 2⟩ := by
    have h := second_half (2 * n + 1) 0 0
    simp only [Nat.zero_add] at h
    convert h using 1; ring_nf
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 h4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 3, n + 1⟩) 0
  intro n; exists 2 * n + 1
  have h := main_trans n
  convert h using 1; ring_nf

end Sz22_2003_unofficial_1084
