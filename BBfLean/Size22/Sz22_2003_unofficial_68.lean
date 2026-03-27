import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #68: [1/18, 2/35, 715/2, 1/5, 21/11, 2/13]

Vector representation:
```
-1 -2  0  0  0  0
 1  0 -1 -1  0  0
-1  0  1  0  1  1
 0  0 -1  0  0  0
 0  1  0  1 -1  0
 1  0  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_68

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

theorem r5_chain : ∀ k b d e f, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih (b + 1) (d + 1) e f)
  ring_nf; finish

theorem r6r1_even : ∀ K d f, ⟨0, 2 * K, 0, d, 0, f + K⟩ [fm]⊢* ⟨0, 0, 0, d, 0, f⟩ := by
  intro K; induction' K with K ih <;> intro d f
  · simp; exists 0
  rw [show 2 * (K + 1) = 2 * K + 2 from by ring,
      show f + (K + 1) = (f + K) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih d f)
  ring_nf; finish

theorem r6r1_odd : ∀ K d f, ⟨0, 2 * K + 1, 0, d, 0, f + K⟩ [fm]⊢* ⟨0, 1, 0, d, 0, f⟩ := by
  intro K; induction' K with K ih <;> intro d f
  · simp; exists 0
  rw [show 2 * (K + 1) + 1 = (2 * K + 1) + 2 from by ring,
      show f + (K + 1) = (f + K) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih d f)
  ring_nf; finish

theorem r3r2_b0 : ∀ k d e f, ⟨1, 0, 0, d + k, e, f⟩ [fm]⊢* ⟨1, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih d (e + 1) (f + 1))
  ring_nf; finish

theorem r3r2_b1 : ∀ k d e f, ⟨1, 1, 0, d + k, e, f⟩ [fm]⊢* ⟨1, 1, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (ih d (e + 1) (f + 1))
  ring_nf; finish

-- (0,0,0,0,2M,G+M+1) ->* (0,0,0,0,2M+1,G+2M+1)
theorem even_phase (M G : ℕ) :
    ⟨0, 0, 0, 0, 2*M, G+M+1⟩ [fm]⊢* ⟨0, 0, 0, 0, 2*M+1, G+2*M+1⟩ := by
  have h1 := r5_chain (2*M) 0 0 0 (G+M+1)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  have h2 := r6r1_even M (2*M) (G+1)
  rw [show G+1+M = G+M+1 from by ring] at h2
  apply stepStar_trans h2
  step fm
  have h3 := r3r2_b0 (2*M) 0 0 G
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  step fm; step fm
  finish

-- (0,0,0,0,2M+1,G+M+1) ->* (0,1,0,0,2M+2,G+2M+2)
theorem odd_phase (M G : ℕ) :
    ⟨0, 0, 0, 0, 2*M+1, G+M+1⟩ [fm]⊢* ⟨0, 1, 0, 0, 2*M+2, G+2*M+2⟩ := by
  have h1 := r5_chain (2*M+1) 0 0 0 (G+M+1)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  have h2 := r6r1_odd M (2*M+1) (G+1)
  rw [show G+1+M = G+M+1 from by ring] at h2
  apply stepStar_trans h2
  step fm
  have h3 := r3r2_b1 (2*M+1) 0 0 G
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  step fm; step fm
  ring_nf; finish

-- (0,1,0,0,2M,G+M+1) ->* (0,1,0,0,2M+1,G+2M+1)
theorem even_phase_b1 (M G : ℕ) :
    ⟨0, 1, 0, 0, 2*M, G+M+1⟩ [fm]⊢* ⟨0, 1, 0, 0, 2*M+1, G+2*M+1⟩ := by
  have h1 := r5_chain (2*M) 1 0 0 (G+M+1)
  rw [show 1 + 2*M = 2*M+1 from by ring] at h1
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  have h2 := r6r1_odd M (2*M) (G+1)
  rw [show G+1+M = G+M+1 from by ring] at h2
  apply stepStar_trans h2
  step fm
  have h3 := r3r2_b1 (2*M) 0 0 G
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  step fm; step fm
  ring_nf; finish

-- (0,1,0,0,2M+1,G+M+2) ->* (0,0,0,0,2M+2,G+2M+2)
theorem odd_phase_b1 (M G : ℕ) :
    ⟨0, 1, 0, 0, 2*M+1, G+M+2⟩ [fm]⊢* ⟨0, 0, 0, 0, 2*M+2, G+2*M+2⟩ := by
  have h1 := r5_chain (2*M+1) 1 0 0 (G+M+2)
  rw [show 1 + (2*M+1) = 2*M+2 from by ring] at h1
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  have h2 := r6r1_even (M+1) (2*M+1) (G+1)
  rw [show 2*(M+1) = 2*M+2 from by ring, show G+1+(M+1) = G+M+2 from by ring] at h2
  apply stepStar_trans h2
  step fm
  have h3 := r3r2_b0 (2*M+1) 0 0 G
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  step fm; step fm
  ring_nf; finish

theorem main_trans (k : ℕ) :
    ⟨0, 0, 0, 0, 4+4*k, 4+7*k+4*k^2⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 8+4*k, 15+15*k+4*k^2⟩ := by
  -- Phase A
  have hA : ⟨0, 0, 0, 0, 4+4*k, 4+7*k+4*k^2⟩ [fm]⊢* ⟨0, 0, 0, 0, 5+4*k, 6+9*k+4*k^2⟩ := by
    have := even_phase (2+2*k) (1+5*k+4*k^2); ring_nf at this ⊢; exact this
  apply stepStar_stepPlus_stepPlus hA
  -- Phase B
  have hB : ⟨0, 0, 0, 0, 5+4*k, 6+9*k+4*k^2⟩ [fm]⊢* ⟨0, 1, 0, 0, 6+4*k, 9+11*k+4*k^2⟩ := by
    have := odd_phase (2+2*k) (3+7*k+4*k^2); ring_nf at this ⊢; exact this
  apply stepStar_stepPlus_stepPlus hB
  -- Phase C
  have hC : ⟨0, 1, 0, 0, 6+4*k, 9+11*k+4*k^2⟩ [fm]⊢* ⟨0, 1, 0, 0, 7+4*k, 12+13*k+4*k^2⟩ := by
    have := even_phase_b1 (3+2*k) (5+9*k+4*k^2); ring_nf at this ⊢; exact this
  apply stepStar_stepPlus_stepPlus hC
  -- Phase D
  have hD : ⟨0, 1, 0, 0, 7+4*k, 12+13*k+4*k^2⟩ [fm]⊢* ⟨0, 0, 0, 0, 8+4*k, 15+15*k+4*k^2⟩ := by
    have := odd_phase_b1 (3+2*k) (7+11*k+4*k^2); ring_nf at this ⊢; exact this
  exact stepStar_stepPlus hD (by intro heq; have := congr_arg Prod.snd heq; simp at this)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 4, 4⟩) (by execute fm 35)
  have h0 : (⟨0, 0, 0, 0, 4, 4⟩ : Q) = ⟨0, 0, 0, 0, 4+4*0, 4+7*0+4*0^2⟩ := by simp
  rw [h0]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun k ↦ ⟨0, 0, 0, 0, 4+4*k, 4+7*k+4*k^2⟩) 0
  intro k; refine ⟨k+1, ?_⟩
  have h := main_trans k
  show ⟨0, 0, 0, 0, 4+4*k, 4+7*k+4*k^2⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 4+4*(k+1), 4+7*(k+1)+4*(k+1)^2⟩
  rw [show 4+4*(k+1) = 8+4*k from by ring, show 4+7*(k+1)+4*(k+1)^2 = 15+15*k+4*k^2 from by ring]
  exact h

end Sz22_2003_unofficial_68
