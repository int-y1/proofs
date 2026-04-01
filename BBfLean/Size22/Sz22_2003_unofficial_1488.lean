import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1488: [7/15, 6/77, 1331/3, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 1  1  0 -1 -1
 0 -1  0  0  3
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1488

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R2 chain with c=0: (a, b, 0, d+k, e+k) -> (a+k, b+k, 0, d, e)
theorem r2_chain : ∀ k, ∀ a b d e,
    ⟨a, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a + k, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (b + 1) d e)
    ring_nf; finish

-- R3 drain: b -> e (with c=0, d=0)
theorem r3_drain : ∀ k, ∀ a e,
    ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih a (e + 3))
    ring_nf; finish

-- R4 chain: e -> c (with b=0, d=0)
theorem r4_chain : ∀ k, ∀ a c e,
    ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- R3/R2 interleave + drain.
-- (3*(B+1), 2*B+3, 0, D, 0) -> (3*(B+1)+D, 0, 3*(B+1)+D+1, 0, 1)
theorem big_phase : ∀ D, ∀ B,
    ⟨3 * (B + 1), 2 * B + 3, 0, D, 0⟩ [fm]⊢*
    ⟨3 * (B + 1) + D, 0, 3 * (B + 1) + D + 1, 0, 1⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro B
  rcases D with _ | _ | _ | D
  · -- D = 0
    apply stepStar_trans (r3_drain (2 * B + 3) (3 * (B + 1)) 0)
    rw [show 0 + 3 * (2 * B + 3) = 1 + 2 * (3 * B + 4) from by ring]
    apply stepStar_trans (r4_chain (3 * B + 4) (3 * (B + 1)) 0 1)
    ring_nf; finish
  · -- D = 1
    step fm
    apply stepStar_trans (r2_chain 1 (3 * (B + 1)) (2 * B + 2) 0 2)
    apply stepStar_trans (r3_drain (2 * B + 3) (3 * (B + 1) + 1) 2)
    rw [show 2 + 3 * (2 * B + 3) = 1 + 2 * (3 * B + 5) from by ring]
    apply stepStar_trans (r4_chain (3 * B + 5) (3 * (B + 1) + 1) 0 1)
    ring_nf; finish
  · -- D = 2
    step fm
    apply stepStar_trans (r2_chain 2 (3 * (B + 1)) (2 * B + 2) 0 1)
    apply stepStar_trans (r3_drain (2 * B + 4) (3 * (B + 1) + 2) 1)
    rw [show 1 + 3 * (2 * B + 4) = 1 + 2 * (3 * B + 6) from by ring]
    apply stepStar_trans (r4_chain (3 * B + 6) (3 * (B + 1) + 2) 0 1)
    ring_nf; finish
  · -- D + 3
    step fm
    apply stepStar_trans (r2_chain 3 (3 * (B + 1)) (2 * B + 2) D 0)
    rw [show 3 * (B + 1) + 3 = 3 * ((B + 1) + 1) from by ring,
        show 2 * B + 2 + 3 = 2 * ((B + 1)) + 3 from by ring,
        show (B + 1) + 1 = B + 1 + 1 from rfl]
    apply stepStar_trans (ih D (by omega) (B + 1))
    ring_nf; finish

-- Drain phase: (A+1, 0, A+2, 0, 1) -> (1, 0, 0, 2*A+2, 0)
-- R5, R1, R2, R1: (A+1, 0, A+2, 0, 1) -> (A+1, 0, A, 2, 0)
-- Then R5+R1 chain A times: (A+1, 0, A, 2, 0) -> (1, 0, 0, 2*A+2, 0)
theorem drain_init (A : ℕ) :
    ⟨A + 1, 0, A + 2, 0, 1⟩ [fm]⊢* ⟨A + 1, 0, A, 2, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

theorem drain_phase : ∀ k, ∀ c d,
    ⟨k + 1, 0, c + k, d, 0⟩ [fm]⊢* ⟨1, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show (k + 1) + 1 = k + 1 + 1 from rfl,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih c (d + 2))
    ring_nf; finish

theorem full_drain (A : ℕ) :
    ⟨A + 1, 0, A + 2, 0, 1⟩ [fm]⊢* ⟨1, 0, 0, 2 * A + 2, 0⟩ := by
  apply stepStar_trans (drain_init A)
  have h := drain_phase A 0 2
  rw [show 0 + A = A from by ring] at h
  apply stepStar_trans h
  ring_nf; finish

-- Combine big_phase and full_drain
theorem mid_to_end (d : ℕ) :
    ⟨3, 3, 0, d, 0⟩ [fm]⊢* ⟨1, 0, 0, 2 * d + 6, 0⟩ := by
  have h1 := big_phase d 0
  rw [show 3 * (0 + 1) = 3 from by ring,
      show 2 * 0 + 3 = 3 from by ring] at h1
  have h2 := full_drain (d + 2)
  rw [show (d + 2) + 1 = 3 + d from by ring,
      show (d + 2) + 2 = 3 + d + 1 from by ring,
      show 2 * (d + 2) + 2 = 2 * d + 6 from by ring] at h2
  exact stepStar_trans h1 h2

-- Full transition: (1, 0, 0, d+2, 0) ⊢⁺ (1, 0, 0, 2*d+6, 0)
theorem full_trans (d : ℕ) :
    ⟨1, 0, 0, d + 2, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 2 * d + 6, 0⟩ := by
  step fm; step fm
  rw [show d + 2 + 1 = d + 3 from by ring]
  apply stepStar_trans (r2_chain 3 0 0 d 0)
  show ⟨3, 3, 0, d, 0⟩ [fm]⊢* _
  exact mid_to_end d

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 0⟩) (by execute fm 10)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun d ↦ ⟨1, 0, 0, d + 2, 0⟩) 0
  intro d; exact ⟨2 * d + 4, full_trans d⟩

end Sz22_2003_unofficial_1488
