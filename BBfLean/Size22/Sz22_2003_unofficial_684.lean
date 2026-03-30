import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #684: [35/6, 4/55, 11/2, 3/7, 12/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 2  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_684

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

-- Single step as stepStar
private theorem one_step (h : fm c₁ = some c₂) : c₁ [fm]⊢* c₂ := ⟨1, h⟩

-- R3 chain: move a to e.
theorem a_to_e : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a d (e + 1)); ring_nf; finish

-- R4 chain: move d to b.
theorem d_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d e); ring_nf; finish

-- R1,R1,R2 interleaved chain.
theorem r1r1r2_chain : ∀ k, ∀ b c d e, ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e); ring_nf; finish

-- R2 chain: drain c and e simultaneously.
theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 2) c d e); ring_nf; finish

-- Even case: (2, 2*m+2, 0, 0, 2*m+1) ->* (2*m+3, 0, 0, 2*m+2, 0)
theorem even_tail : ⟨2, 2 * m + 2, 0, 0, 2 * m + 1⟩ [fm]⊢* ⟨2 * m + 3, 0, 0, 2 * m + 2, 0⟩ := by
  apply stepStar_trans
  · rw [show 2 * m + 2 = 2 + 2 * m from by ring,
        show 2 * m + 1 = (m + 1) + m from by ring]
    exact r1r1r2_chain m 2 0 0 (m + 1)
  apply stepStar_trans (c₂ := ⟨1, 1, m + 1, 2 * m + 1, m + 1⟩)
  · exact one_step (by rw [show 0 + m = m from by ring, show 0 + 2 * m = 2 * m from by ring]; simp [fm])
  apply stepStar_trans (c₂ := ⟨0, 0, m + 2, 2 * m + 2, m + 1⟩)
  · exact one_step (by simp [fm])
  apply stepStar_trans (c₂ := ⟨2 * m + 2, 0, 1, 2 * m + 2, 0⟩)
  · have h := r2_chain (m + 1) 0 1 (2 * m + 2) 0
    rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
        show 1 + (m + 1) = m + 2 from by ring,
        show 0 + (m + 1) = m + 1 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨2 * m + 1, 0, 1, 2 * m + 2, 1⟩)
  · exact one_step (by rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]; simp [fm])
  exact one_step (by rw [show (1 : ℕ) = 0 + 1 from by ring]; simp [fm])

-- Odd case: (2, 2*m+3, 0, 0, 2*m+2) ->* (2*m+4, 0, 0, 2*m+3, 0)
theorem odd_tail : ⟨2, 2 * m + 3, 0, 0, 2 * m + 2⟩ [fm]⊢* ⟨2 * m + 4, 0, 0, 2 * m + 3, 0⟩ := by
  apply stepStar_trans
  · rw [show 2 * m + 3 = 3 + 2 * m from by ring,
        show 2 * m + 2 = (m + 2) + m from by ring]
    exact r1r1r2_chain m 3 0 0 (m + 2)
  apply stepStar_trans (c₂ := ⟨1, 2, m + 1, 2 * m + 1, m + 2⟩)
  · exact one_step (by rw [show 0 + m = m from by ring, show 0 + 2 * m = 2 * m from by ring]; simp [fm])
  apply stepStar_trans (c₂ := ⟨0, 1, m + 2, 2 * m + 2, m + 2⟩)
  · exact one_step (by simp [fm])
  apply stepStar_trans (c₂ := ⟨2, 1, m + 1, 2 * m + 2, m + 1⟩)
  · exact one_step (by rw [show m + 2 = (m + 1) + 1 from by ring]; simp [fm])
  apply stepStar_trans (c₂ := ⟨1, 0, m + 2, 2 * m + 3, m + 1⟩)
  · exact one_step (by simp [fm])
  apply stepStar_trans (c₂ := ⟨2 * m + 3, 0, 1, 2 * m + 3, 0⟩)
  · have h := r2_chain (m + 1) 1 1 (2 * m + 3) 0
    rw [show 1 + 2 * (m + 1) = 2 * m + 3 from by ring,
        show 1 + (m + 1) = m + 2 from by ring,
        show 0 + (m + 1) = m + 1 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨2 * m + 2, 0, 1, 2 * m + 3, 1⟩)
  · exact one_step (by rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]; simp [fm])
  exact one_step (by rw [show (1 : ℕ) = 0 + 1 from by ring]; simp [fm])

-- Phases 1-3: (n+2, 0, 0, n+1, 0) ⊢⁺ (2, n+2, 0, 0, n+1)
theorem phases_1_to_3 : ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨2, n + 2, 0, 0, n + 1⟩ := by
  apply step_stepStar_stepPlus (c₂ := ⟨n + 1, 0, 0, n + 1, 1⟩)
  · exact (show ⟨(n + 1) + 1, 0, 0, n + 1, 0⟩ [fm]⊢ _ from by simp [fm])
  apply stepStar_trans (c₂ := ⟨0, 0, 0, n + 1, n + 2⟩)
  · have h := a_to_e (n + 1) 0 (n + 1) 1
    rw [show 0 + (n + 1) = n + 1 from by ring, show 1 + (n + 1) = n + 2 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨0, n + 1, 0, 0, n + 2⟩)
  · have h := d_to_b (n + 1) 0 0 (n + 2)
    rw [show 0 + (n + 1) = n + 1 from by ring] at h
    exact h
  exact one_step (by rw [show n + 2 = (n + 1) + 1 from by ring]; simp [fm])

-- Main transition
theorem main_trans : ⟨n + 2, 0, 0, n + 1, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, n + 2, 0⟩ := by
  apply stepPlus_stepStar_stepPlus phases_1_to_3
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact even_tail
  · subst hm
    rw [show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show 2 * m + 1 + 3 = 2 * m + 4 from by ring]
    exact odd_tail

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 0
  intro n; exists n + 1; exact main_trans
