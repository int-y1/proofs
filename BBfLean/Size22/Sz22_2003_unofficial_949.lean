import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #949: [4/15, 33/14, 275/2, 7/11, 33/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 0  1 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_949

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c d e,
    ⟨a + 1, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c d (e + 1))
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b e,
    ⟨a + k, b, 0, k, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 1))
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) (e + 1)); ring_nf; finish

theorem b_r3_combined : ∀ b, ∀ a e,
    ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a + 3 * b + 2, 0, e + a + 2 * b + 1⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a e
  rcases b with _ | _ | b
  · -- b = 0: R3 drain
    have h := r3_drain (a + 1) 0 e
    simp only [Nat.zero_add] at h
    convert h using 2
  · -- b = 1: R3, R1, then R3 drain
    step fm; step fm
    have h := r3_drain (a + 2) 1 (e + 1)
    apply stepStar_trans h
    ring_nf; finish
  · -- b + 2: R3, R1, R1, then recurse
    rw [show (b : ℕ) + 1 + 1 = (b + 1) + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (by omega) (a + 3) (e + 1))
    ring_nf; finish

theorem main_trans (p q : ℕ) :
    ⟨0, 0, p + q + 5, 0, p + 2 * q + 5⟩ [fm]⊢⁺
    ⟨0, 0, 2 * p + 3 * q + 12, 0, 2 * p + 4 * q + 13⟩ := by
  -- Phase 1 (R4 drain): (0,0,C,0,E) -> (0,0,C,E,0)
  have phase1 : ⟨0, 0, p + q + 5, 0, p + 2 * q + 5⟩ [fm]⊢*
      ⟨0, 0, p + q + 5, p + 2 * q + 5, 0⟩ := by
    have h := r4_drain (p + 2 * q + 5) (p + q + 5) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2 (R5): (0,0,C,E,0) -> (0,1,C-1,E,1)
  have phase2 : ⟨0, 0, p + q + 5, p + 2 * q + 5, 0⟩ [fm]⊢*
      ⟨0, 1, p + q + 4, p + 2 * q + 5, 1⟩ := by
    rw [show p + q + 5 = (p + q + 4) + 1 from by ring]
    step fm; finish
  -- Phase 3 (R1): (0,1,C-1,E,1) -> (2,0,C-2,E,1)
  have phase3 : ⟨0, 1, p + q + 4, p + 2 * q + 5, 1⟩ [fm]⊢*
      ⟨2, 0, p + q + 3, p + 2 * q + 5, 1⟩ := by
    rw [show p + q + 4 = (p + q + 3) + 1 from by ring]
    step fm; finish
  -- Phase 4 (R2/R1 chain, p+q+3 rounds):
  -- (2,0,p+q+3, p+2q+5, 1) -> (p+q+5, 0, 0, q+2, p+q+4)
  have phase4 : ⟨2, 0, p + q + 3, p + 2 * q + 5, 1⟩ [fm]⊢*
      ⟨p + q + 5, 0, 0, q + 2, p + q + 4⟩ := by
    have h := r2r1_chain (p + q + 3) 1 0 (q + 2) 1
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 5 (R2 drain, q+2 rounds):
  -- (p+q+5, 0, 0, q+2, p+q+4) -> (p+3, q+2, 0, 0, p+2q+6)
  have phase5 : ⟨p + q + 5, 0, 0, q + 2, p + q + 4⟩ [fm]⊢*
      ⟨p + 3, q + 2, 0, 0, p + 2 * q + 6⟩ := by
    have h := r2_drain (q + 2) (p + 3) 0 (p + q + 4)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf
  -- Phase 6 (b_r3_combined):
  -- (p+3, q+2, 0, 0, p+2q+6) -> (0, 0, 2p+3q+12, 0, 2p+4q+13)
  have phase6 : ⟨p + 3, q + 2, 0, 0, p + 2 * q + 6⟩ [fm]⊢*
      ⟨0, 0, 2 * p + 3 * q + 12, 0, 2 * p + 4 * q + 13⟩ := by
    have h := b_r3_combined (q + 2) (p + 2) (p + 2 * q + 6)
    convert h using 2; ring_nf
  -- Compose all phases
  have combined : ⟨0, 0, p + q + 5, 0, p + 2 * q + 5⟩ [fm]⊢*
      ⟨0, 0, 2 * p + 3 * q + 12, 0, 2 * p + 4 * q + 13⟩ :=
    stepStar_trans phase1 (stepStar_trans phase2 (stepStar_trans phase3
      (stepStar_trans phase4 (stepStar_trans phase5 phase6))))
  exact stepStar_stepPlus combined (by simp [Q]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 0, 5⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨p, q⟩ ↦ ⟨0, 0, p + q + 5, 0, p + 2 * q + 5⟩) ⟨0, 0⟩
  intro ⟨p, q⟩
  refine ⟨⟨2 * p + 2 * q + 6, q + 1⟩, ?_⟩
  show ⟨0, 0, p + q + 5, 0, p + 2 * q + 5⟩ [fm]⊢⁺
    ⟨0, 0, (2 * p + 2 * q + 6) + (q + 1) + 5, 0, (2 * p + 2 * q + 6) + 2 * (q + 1) + 5⟩
  rw [show (2 * p + 2 * q + 6) + (q + 1) + 5 = 2 * p + 3 * q + 12 from by ring,
      show (2 * p + 2 * q + 6) + 2 * (q + 1) + 5 = 2 * p + 4 * q + 13 from by ring]
  exact main_trans p q

end Sz22_2003_unofficial_949
