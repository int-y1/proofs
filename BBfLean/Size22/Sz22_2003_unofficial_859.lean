import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #859: [385/6, 4/65, 91/2, 3/11, 55/7]

Vector representation:
```
-1 -1  1  1  1  0
 2  0 -1  0  0 -1
-1  0  0  1  0  1
 0  1  0  0 -1  0
 0  0  1 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_859

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (d + 1) e (f + 1)); ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d e f); ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b c D e f, ⟨2, b + 2 * k, c, D, e, f + k⟩ [fm]⊢* ⟨2, b, c + k, D + 2 * k, e + 2 * k, f⟩ := by
  intro k; induction' k with k ih <;> intro b c D e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c D e (f + 1))
    rw [show b + 2 = (b + 1) + 1 from by ring]
    step fm; step fm; step fm; ring_nf; finish

theorem r2_drain : ∀ k, ∀ a c D e f, ⟨a, 0, c + k, D, e, f + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, D, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c D e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring, show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 2) c D e f); ring_nf; finish

theorem interleaved_even (m D : ℕ) : ⟨2, 2 * m, 0, D, 1, 2 * m⟩ [fm]⊢* ⟨2 + 2 * m, 0, 0, D + 2 * m, 1 + 2 * m, 0⟩ := by
  have h1 := r1r1r2_chain m 0 0 D 1 m
  have h2 := r2_drain m 2 0 (D + 2 * m) (1 + 2 * m) 0
  simp only [Nat.zero_add] at h1 h2
  rw [show (m + m : ℕ) = 2 * m from by ring] at h1
  exact stepStar_trans h1 h2

theorem interleaved_odd (m D : ℕ) : ⟨2, 2 * m + 1, 0, D, 1, 2 * m + 1⟩ [fm]⊢* ⟨3 + 2 * m, 0, 0, D + 2 * m + 1, 2 + 2 * m, 0⟩ := by
  have h1 := r1r1r2_chain m 1 0 D 1 (m + 1)
  simp only [Nat.zero_add] at h1
  rw [show (1 + 2 * m : ℕ) = 2 * m + 1 from by ring,
      show ((m + 1) + m : ℕ) = 2 * m + 1 from by ring] at h1
  apply stepStar_trans h1
  apply stepStar_trans
  · show ⟨2, 1, m, D + 2 * m, 2 * m + 1, m + 1⟩ [fm]⊢* ⟨1, 0, m + 1, D + 2 * m + 1, 2 + 2 * m, m + 1⟩
    rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm; ring_nf; finish
  have h2 := r2_drain (m + 1) 1 0 (D + 2 * m + 1) (2 * m + 2) 0
  simp only [Nat.zero_add] at h2
  rw [show (1 + 2 * (m + 1) : ℕ) = 3 + 2 * m from by ring,
      show (2 * m + 2 : ℕ) = 2 + 2 * m from by ring] at h2
  exact h2

-- Full transition: C(n) = (n+2, 0, 0, n*(n+1), n+1, 0) ⊢⁺ C(n+1)
theorem main_transition (n : ℕ) : ⟨n + 2, 0, 0, n * (n + 1), n + 1, 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, (n + 1) * (n + 2), n + 2, 0⟩ := by
  suffices h : ⟨n + 2, 0, 0, n * (n + 1), n + 1, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, (n + 1) * (n + 2), n + 2, 0⟩ by
    exact stepStar_stepPlus h (by intro heq; have := congr_arg Prod.fst heq; omega)
  -- Phase 1: R3 chain
  have p1 := r3_chain (n + 2) 0 (n * (n + 1)) (n + 1) 0
  simp only [Nat.zero_add] at p1
  apply stepStar_trans p1
  -- State: (0, 0, 0, n*(n+1)+(n+2), n+1, n+2)
  -- Phase 2: R4 chain
  have p2 := r4_chain (n + 1) 0 (n * (n + 1) + (n + 2)) 0 (n + 2)
  simp only [Nat.zero_add] at p2
  apply stepStar_trans p2
  -- State: (0, n+1, 0, n*(n+1)+(n+2), 0, n+2)
  -- Phase 3: R5
  apply stepStar_trans
  · show ⟨0, n + 1, 0, n * (n + 1) + (n + 2), 0, n + 2⟩ [fm]⊢*
         ⟨0, n + 1, 1, n * (n + 1) + (n + 1), 1, n + 2⟩
    rw [show n * (n + 1) + (n + 2) = (n * (n + 1) + (n + 1)) + 1 from by ring]
    step fm; finish
  -- Phase 4: R2
  apply stepStar_trans
  · show ⟨0, n + 1, 1, n * (n + 1) + (n + 1), 1, n + 2⟩ [fm]⊢*
         ⟨2, n + 1, 0, n * (n + 1) + (n + 1), 1, n + 1⟩
    rw [show (n + 2 : ℕ) = (n + 1) + 1 from by ring]
    step fm; ring_nf; finish
  -- Phase 5: interleaved
  -- State: (2, n+1, 0, n*(n+1)+(n+1), 1, n+1)
  set D := n * (n + 1) + (n + 1) with hD
  rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n+1 = m+m = 2*m
    rw [show m + m = 2 * m from by ring] at hm
    have h5 := interleaved_even m D
    rw [← hm] at h5
    apply stepStar_trans h5
    -- Goal has (2+(n+1), 0, 0, D+(n+1), 1+(n+1), 0) ⊢* (n+3, 0, 0, (n+1)*(n+2), n+2, 0)
    have hD2 : D + (n + 1) = (n + 1) * (n + 2) := by rw [hD]; ring
    rw [show 2 + (n + 1) = n + 3 from by ring,
        hD2,
        show 1 + (n + 1) = n + 2 from by ring]
    finish
  · -- n+1 = 2*m+1
    have h5 := interleaved_odd m D
    rw [← hm] at h5
    apply stepStar_trans h5
    -- Goal has (3+2*m, 0, 0, D+2*m+1, 2+2*m, 0) ⊢* (n+3, 0, 0, (n+1)*(n+2), n+2, 0)
    have hD2 : D + 2 * m + 1 = (n + 1) * (n + 2) := by
      rw [hD, show 2 * m = n from by omega]; ring
    rw [show 3 + 2 * m = n + 3 from by omega,
        hD2,
        show 2 + 2 * m = n + 2 from by omega]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1, 0⟩)
  · execute fm 3
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n * (n + 1), n + 1, 0⟩) 0
  intro n; exact ⟨n + 1, main_transition n⟩
