import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #107: [7/30, 44/21, 9/2, 5/11, 7/3]

Vector representation:
```
-1 -1 -1  1  0
 2 -1  0 -1  1
-1  2  0  0  0
 0  0  1  0 -1
 0 -1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_107

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R3 repeated: a → b
theorem a_to_b : ⟨a+k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b+2*k, 0, 0, e⟩ := by
  have many_step : ∀ k a b, ⟨a+k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b+2*k, 0, 0, e⟩ := by
    intro k; induction' k with k h <;> intro a b
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k a b

-- R4 repeated: e → c
theorem e_to_c : ⟨0, b, c, 0, e+k⟩ [fm]⊢* ⟨0, b, c+k, 0, e⟩ := by
  have many_step : ∀ k c e, ⟨0, b, c, 0, e+k⟩ [fm]⊢* ⟨0, b, c+k, 0, e⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (h _ _)
    ring_nf; finish
  exact many_step k c e

-- R2 repeated: b,d → a,e
theorem r2_chain : ⟨a, b+k, 0, d+k, e⟩ [fm]⊢* ⟨a+2*k, b, 0, d, e+k⟩ := by
  have many_step : ∀ k a b d e, ⟨a, b+k, 0, d+k, e⟩ [fm]⊢* ⟨a+2*k, b, 0, d, e+k⟩ := by
    intro k; induction' k with k h <;> intro a b d e
    · exists 0
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (h _ _ _ _)
    ring_nf; finish
  exact many_step k a b d e

-- R1R1R2 rounds
theorem r1r1r2_rounds : ∀ k, ∀ b c d e, ⟨2, b+3*k, c+2*k, d, e⟩ [fm]⊢* ⟨2, b, c, d+k, e+k⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  rw [show (b + 3 * k) + 3 = ((b + 3 * k) + 2) + 1 from by ring,
      show (c + 2 * k) + 2 = ((c + 2 * k) + 1) + 1 from by ring]
  step fm
  rw [show (b + 3 * k) + 2 = ((b + 3 * k) + 1) + 1 from by ring,
      show (c + 2 * k) + 1 = (c + 2 * k) + 1 from by ring]
  step fm
  rw [show (b + 3 * k) + 1 = (b + 3 * k) + 1 from by ring,
      show d + 2 = (d + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (h b c (d + 1) (e + 1))
  ring_nf; finish

-- Odd tail
theorem odd_tail : ∀ m, ⟨2, m+2, 1, m, m+1⟩ [fm]⊢* ⟨2*m+3, 0, 0, 0, 2*m+2⟩ := by
  intro m
  rw [show m + 2 = (m + 1) + 1 from by ring]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨1 + 1, (m + 1) + 1, 0 + 1, m, m + 1⟩ = some ⟨1, m + 1, 0, m + 1, m + 1⟩
    simp [fm]
  have h := @r2_chain 1 0 (m + 1) 0 (m + 1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Even tail
theorem even_tail : ∀ m, ⟨2, m+4, 2, m, m+1⟩ [fm]⊢* ⟨2*m+4, 0, 0, 0, 2*m+3⟩ := by
  intro m
  rw [show m + 4 = (m + 3) + 1 from by ring]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨1 + 1, (m + 3) + 1, 1 + 1, m, m + 1⟩ = some ⟨1, m + 3, 1, m + 1, m + 1⟩
    simp [fm]
  rw [show m + 3 = (m + 2) + 1 from by ring]
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨0 + 1, (m + 2) + 1, 0 + 1, m + 1, m + 1⟩ = some ⟨0, m + 2, 0, m + 2, m + 1⟩
    simp [fm]
  have h := @r2_chain 0 0 (m + 2) 0 (m + 1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition: (n+1, 0, 0, 0, n) →⁺ (n+2, 0, 0, 0, n+1)
theorem main_trans : ⟨n+1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, n+1⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*(n+1), 0, 0, n⟩)
  · have h := @a_to_b 0 (n + 1) 0 n
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 2*(n+1), n, 0, 0⟩)
  · have h := @e_to_c (2 * (n + 1)) 0 0 n
    simp only [Nat.zero_add] at h; exact h
  rcases n with _ | n'
  · execute fm 2
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 2*n'+2, n'+1, 0, 1⟩)
  · apply stepStar_trans
    · apply step_stepStar
      show fm ⟨0, (2 * n' + 3) + 1, n' + 1, 0, 0⟩ = some ⟨0, 2 * n' + 3, n' + 1, 1, 0⟩
      simp [fm]
    apply step_stepStar
    show fm ⟨0, (2 * n' + 2) + 1, n' + 1, 0 + 1, 0⟩ = some ⟨2, 2 * n' + 2, n' + 1, 0, 1⟩
    simp [fm]
  rcases Nat.even_or_odd n' with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n' = 2m, so n'+1 = 2m+1 (odd case)
    subst hm
    show (⟨2, 2*(m+m)+2, m+m+1, 0, 1⟩ : Q) [fm]⊢⁺ ⟨m+m+1+2, 0, 0, 0, m+m+1+1⟩
    have h1 : (⟨2, 4*m+2, 2*m+1, 0, 1⟩ : Q) [fm]⊢* ⟨2, m+2, 1, m, m+1⟩ := by
      have h := @r1r1r2_rounds m (m + 2) 1 0 1
      simp only [Nat.zero_add] at h
      rw [show m + 2 + 3 * m = 4 * m + 2 from by ring,
          show 1 + 2 * m = 2 * m + 1 from by ring,
          show 1 + m = m + 1 from by ring] at h
      exact h
    have h2 : (⟨2, m+2, 1, m, m+1⟩ : Q) [fm]⊢* ⟨2*m+3, 0, 0, 0, 2*m+2⟩ := odd_tail m
    have h3 : (⟨2, 4*m+2, 2*m+1, 0, 1⟩ : Q) [fm]⊢* ⟨2*m+3, 0, 0, 0, 2*m+2⟩ :=
      stepStar_trans h1 h2
    have h4 : (⟨2, 4*m+2, 2*m+1, 0, 1⟩ : Q) ≠ ⟨2*m+3, 0, 0, 0, 2*m+2⟩ := by
      intro h; simp [Prod.mk.injEq] at h
    have h5 := stepStar_stepPlus h3 h4
    rw [show (⟨2, 4*m+2, 2*m+1, 0, 1⟩ : Q) = ⟨2, 2*(m+m)+2, m+m+1, 0, 1⟩ from by ring_nf,
        show (⟨2*m+3, 0, 0, 0, 2*m+2⟩ : Q) = ⟨m+m+1+2, 0, 0, 0, m+m+1+1⟩ from by ring_nf] at h5
    exact h5
  · -- n' = 2m+1, so n'+1 = 2m+2 (even case)
    subst hm
    show (⟨2, 2*(2*m+1)+2, 2*m+1+1, 0, 1⟩ : Q) [fm]⊢⁺ ⟨2*m+1+1+2, 0, 0, 0, 2*m+1+1+1⟩
    have h1 : (⟨2, 4*m+4, 2*m+2, 0, 1⟩ : Q) [fm]⊢* ⟨2, m+4, 2, m, m+1⟩ := by
      have h := @r1r1r2_rounds m (m + 4) 2 0 1
      simp only [Nat.zero_add] at h
      rw [show m + 4 + 3 * m = 4 * m + 4 from by ring,
          show 2 + 2 * m = 2 * m + 2 from by ring,
          show 1 + m = m + 1 from by ring] at h
      exact h
    have h2 : (⟨2, m+4, 2, m, m+1⟩ : Q) [fm]⊢* ⟨2*m+4, 0, 0, 0, 2*m+3⟩ := even_tail m
    have h3 : (⟨2, 4*m+4, 2*m+2, 0, 1⟩ : Q) [fm]⊢* ⟨2*m+4, 0, 0, 0, 2*m+3⟩ :=
      stepStar_trans h1 h2
    have h4 : (⟨2, 4*m+4, 2*m+2, 0, 1⟩ : Q) ≠ ⟨2*m+4, 0, 0, 0, 2*m+3⟩ := by
      intro h; simp [Prod.mk.injEq] at h
    have h5 := stepStar_stepPlus h3 h4
    rw [show (⟨2, 4*m+4, 2*m+2, 0, 1⟩ : Q) = ⟨2, 2*(2*m+1)+2, 2*m+1+1, 0, 1⟩ from by ring_nf,
        show (⟨2*m+4, 0, 0, 0, 2*m+3⟩ : Q) = ⟨2*m+1+1+2, 0, 0, 0, 2*m+1+1+1⟩ from by ring_nf] at h5
    exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 0, n⟩) 0
  intro n; exact ⟨n+1, main_trans⟩
