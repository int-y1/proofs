import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1135: [5/6, 44/35, 49/2, 3/11, 605/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  2  0
 0  1  0  0 -1
 0  0  1 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1135

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

theorem e_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 2) e)
    ring_nf; finish

theorem drain_by_2 : ∀ k, ∀ r c d e,
    ⟨0, 2 * k + r, c + 1, d + k, e⟩ [fm]⊢* ⟨0, r, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro r c d e
  · simp; exists 0
  · rw [show 2 * (k + 1) + r = (2 * k + r + 1) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show 2 * k + r + 1 = (2 * k + r) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih r (c + 1) d (e + 1))
    ring_nf; finish

theorem handle_b1 (c d e : ℕ) :
    ⟨0, 1, c + 1, d + c + 2, e⟩ [fm]⊢* ⟨2 * c + 3, 0, 0, d, e + c + 2⟩ := by
  rw [show d + c + 2 = (d + c + 1) + 1 from by ring]
  step fm
  step fm
  show ⟨1, 0, c + 1, d + c + 1, e + 1⟩ [fm]⊢* ⟨2 * c + 3, 0, 0, d, e + c + 2⟩
  rw [show c + 1 = 0 + (c + 1) from by ring,
      show d + c + 1 = d + (c + 1) from by ring]
  apply stepStar_trans (r2_chain (c + 1) 1 0 d (e + 1))
  ring_nf; finish

theorem middle_phase (B d : ℕ) :
    ⟨0, B, 1, d + B + 1, 2⟩ [fm]⊢* ⟨B + 2, 0, 0, d, B + 3⟩ := by
  rcases Nat.even_or_odd B with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- B = 2*K (even)
    rw [show K + K = 2 * K from by ring] at hK; subst hK
    rw [show d + 2 * K + 1 = (d + K + 1) + K from by ring]
    apply stepStar_trans (drain_by_2 K 0 0 (d + K + 1) 2)
    -- After drain: (0, 0, 0+K+1, d+K+1, 2+K)
    -- Need to match r2_chain form: (a, 0, c+k, d'+k, e')
    -- With a=0, c=0, k=K+1, d'=d, e'=K+2
    show ⟨0, 0, 0 + K + 1, d + K + 1, 2 + K⟩ [fm]⊢* ⟨2 * K + 2, 0, 0, d, 2 * K + 3⟩
    rw [show 0 + K + 1 = 0 + (K + 1) from by ring,
        show d + K + 1 = d + (K + 1) from by ring,
        show 2 + K = K + 2 from by ring]
    apply stepStar_trans (r2_chain (K + 1) 0 0 d (K + 2))
    ring_nf; finish
  · -- B = 2*K + 1 (odd)
    subst hK
    rw [show d + (2 * K + 1) + 1 = (d + K + 2) + K from by ring]
    apply stepStar_trans (drain_by_2 K 1 0 (d + K + 2) 2)
    -- After drain: (0, 1, 0+K+1, d+K+2, 2+K)
    show ⟨0, 1, 0 + K + 1, d + K + 2, 2 + K⟩ [fm]⊢* ⟨2 * K + 1 + 2, 0, 0, d, 2 * K + 1 + 3⟩
    rw [show 0 + K + 1 = K + 1 from by ring,
        show 2 + K = K + 2 from by ring]
    apply stepStar_trans (handle_b1 K d (K + 2))
    ring_nf; finish

def D : ℕ → ℕ
  | 0 => 9
  | n + 1 => D n + 3 * n + 8

theorem D_decomp (n : ℕ) : ∃ d, D n = d + (3 * n + 8) := by
  induction' n with n ih
  · exact ⟨1, by simp [D]⟩
  · obtain ⟨d', hd'⟩ := ih
    refine ⟨d' + 3 * n + 5, ?_⟩
    show D n + 3 * n + 8 = d' + 3 * n + 5 + (3 * (n + 1) + 8)
    rw [hd']; ring

theorem main_transition (n : ℕ) :
    ⟨0, 0, 0, D n, 3 * n + 6⟩ [fm]⊢⁺ ⟨0, 0, 0, D (n + 1), 3 * (n + 1) + 6⟩ := by
  obtain ⟨d, hd⟩ := D_decomp n
  -- Phase 1: e_to_b
  -- (0, 0, 0, D n, 3*n+6) →* (0, 3*n+6, 0, D n, 0)
  rw [hd, show (3 * n + 6 : ℕ) = 0 + (3 * n + 6) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (3 * n + 6) 0 (d + (3 * n + 8)) 0)
  -- Phase 2: R5 step
  -- (0, 3*n+6, 0, d+3*n+8, 0) → (0, 3*n+6, 1, d+3*n+7, 2)
  show ⟨0, 0 + (3 * n + 6), 0, d + (3 * n + 8), 0⟩ [fm]⊢⁺ ⟨0, 0, 0, D (n + 1), 3 * (n + 1) + 6⟩
  rw [show 0 + (3 * n + 6) = 3 * n + 6 from by ring,
      show d + (3 * n + 8) = (d + 3 * n + 7) + 1 from by ring]
  apply step_stepStar_stepPlus (by rfl : (⟨0, 3 * n + 6, 0, (d + 3 * n + 7) + 1, 0⟩ : Q) [fm]⊢
      ⟨0, 3 * n + 6, 1, d + 3 * n + 7, 2⟩)
  -- Phase 3: middle_phase
  -- (0, 3*n+6, 1, d+3*n+7, 2) →* (3*n+8, 0, 0, d, 3*n+9)
  rw [show d + 3 * n + 7 = d + (3 * n + 6) + 1 from by ring]
  apply stepStar_trans (middle_phase (3 * n + 6) d)
  -- Phase 4: r3_chain
  -- (3*n+8, 0, 0, d, 3*n+9) →* (0, 0, 0, d+6*n+16, 3*n+9)
  show ⟨(3 * n + 6) + 2, 0, 0, d, (3 * n + 6) + 3⟩ [fm]⊢* ⟨0, 0, 0, D (n + 1), 3 * (n + 1) + 6⟩
  rw [show (3 * n + 6) + 2 = 0 + (3 * n + 8) from by ring,
      show (3 * n + 6) + 3 = 3 * (n + 1) + 6 from by ring]
  apply stepStar_trans (r3_chain (3 * n + 8) 0 d (3 * (n + 1) + 6))
  -- D(n+1) = D(n) + 3*n + 8 = (d + 3*n + 8) + 3*n + 8 = d + 6*n + 16 = d + 2*(3*n+8)
  show ⟨0, 0, 0, d + 2 * (3 * n + 8), 3 * (n + 1) + 6⟩ [fm]⊢* ⟨0, 0, 0, D (n + 1), 3 * (n + 1) + 6⟩
  have hD : D (n + 1) = d + 2 * (3 * n + 8) := by
    show D n + 3 * n + 8 = d + 2 * (3 * n + 8)
    omega
  rw [hD]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, D 0, 6⟩)
  · show c₀ [fm]⊢* ⟨0, 0, 0, 9, 6⟩
    execute fm 21
  · apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n ↦ ⟨0, 0, 0, D n, 3 * n + 6⟩) 0
    intro n; exact ⟨n + 1, main_transition n⟩
