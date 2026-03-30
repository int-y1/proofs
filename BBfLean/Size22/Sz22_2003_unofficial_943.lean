import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #943: [4/15, 33/14, 275/2, 7/11, 14/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  1
 0  0  0  1 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_943

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

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
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (c + 2) (e + 1))
    ring_nf; finish

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem b_r3_combined : ∀ b, ∀ a e,
    ⟨a + 1, b, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2 * a + 3 * b + 2, 0, e + a + 2 * b + 1⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro a e
  rcases b with _ | _ | b
  · -- b = 0: just R3 drain
    have h := r3_drain (a + 1) 0 e
    simp only [Nat.zero_add] at h
    convert h using 2
  · -- b = 1: (a+1, 1, 0, 0, e)
    -- R3: (a, 1, 2, 0, e+1). R1 (b=1,c=2): (a+2, 0, 1, 0, e+1).
    -- Then R3 drain from (a+2, 0, 1, 0, e+1)
    step fm; step fm
    have h := r3_drain (a + 2) 1 (e + 1)
    apply stepStar_trans h
    ring_nf; finish
  · -- b + 2: (a+1, b+2, 0, 0, e)
    -- R3: (a, b+2, 2, 0, e+1). R1: (a+2, b+1, 1, 0, e+1). R1: (a+4, b, 0, 0, e+1).
    -- = ((a+3)+1, b, 0, 0, e+1). Apply ih b (by omega).
    rw [show (b : ℕ) + 1 + 1 = (b + 1) + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (by omega) (a + 3) (e + 1))
    ring_nf; finish

theorem main_trans (m p : ℕ) :
    ⟨0, 0, m + p + 5, 2 * m + p + 5, 0⟩ [fm]⊢⁺
    ⟨0, 0, 3 * m + 2 * p + 12, 4 * m + 2 * p + 13, 0⟩ := by
  -- Phase 1 (R5): (0,0,m+p+5,2m+p+5,0) → (1,0,m+p+4,2m+p+6,0)
  have phase1 : ⟨0, 0, m + p + 5, 2 * m + p + 5, 0⟩ [fm]⊢*
      ⟨1, 0, m + p + 4, 2 * m + p + 6, 0⟩ := by
    rw [show m + p + 5 = (m + p + 4) + 1 from by ring]
    step fm; finish
  -- Phase 2 (R2/R1 chain, m+p+4 rounds):
  -- (1,0,m+p+4,2m+p+6,0) → (m+p+5,0,0,m+2,m+p+4)
  have phase2 : ⟨1, 0, m + p + 4, 2 * m + p + 6, 0⟩ [fm]⊢*
      ⟨m + p + 5, 0, 0, m + 2, m + p + 4⟩ := by
    have h := r2r1_chain (m + p + 4) 0 0 (m + 2) 0
    simp only [Nat.zero_add] at h
    convert h using 2; (ring_nf)
  -- Phase 3 (R2 drain, m+2 rounds):
  -- (m+p+5,0,0,m+2,m+p+4) → (p+3,m+2,0,0,2m+p+6)
  have phase3 : ⟨m + p + 5, 0, 0, m + 2, m + p + 4⟩ [fm]⊢*
      ⟨p + 3, m + 2, 0, 0, 2 * m + p + 6⟩ := by
    have h := r2_drain (m + 2) (p + 3) 0 (m + p + 4)
    simp only [Nat.zero_add] at h
    convert h using 2; (ring_nf)
  -- Phase 4 (combined b-drain + R3 drain):
  -- (p+3,m+2,0,0,2m+p+6) → (0,0,3m+2p+12,0,4m+2p+13)
  have phase4 : ⟨p + 3, m + 2, 0, 0, 2 * m + p + 6⟩ [fm]⊢*
      ⟨0, 0, 3 * m + 2 * p + 12, 0, 4 * m + 2 * p + 13⟩ := by
    have h := b_r3_combined (m + 2) (p + 2) (2 * m + p + 6)
    convert h using 2; (ring_nf)
  -- Phase 5 (R4 drain):
  -- (0,0,3m+2p+12,0,4m+2p+13) → (0,0,3m+2p+12,4m+2p+13,0)
  have phase5 : ⟨0, 0, 3 * m + 2 * p + 12, 0, 4 * m + 2 * p + 13⟩ [fm]⊢*
      ⟨0, 0, 3 * m + 2 * p + 12, 4 * m + 2 * p + 13, 0⟩ := by
    have h := r4_drain (4 * m + 2 * p + 13) (3 * m + 2 * p + 12) 0
    simp only [Nat.zero_add] at h
    exact h
  -- Compose all phases into ⊢*, then convert to ⊢⁺
  have combined : ⟨0, 0, m + p + 5, 2 * m + p + 5, 0⟩ [fm]⊢*
      ⟨0, 0, 3 * m + 2 * p + 12, 4 * m + 2 * p + 13, 0⟩ :=
    stepStar_trans phase1 (stepStar_trans phase2 (stepStar_trans phase3
      (stepStar_trans phase4 phase5)))
  exact stepStar_stepPlus combined (by simp [Q]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 5, 0⟩) (by execute fm 15)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, p⟩ ↦ ⟨0, 0, m + p + 5, 2 * m + p + 5, 0⟩) ⟨0, 0⟩
  intro ⟨m, p⟩
  refine ⟨⟨m + 1, 2 * m + 2 * p + 6⟩, ?_⟩
  show ⟨0, 0, m + p + 5, 2 * m + p + 5, 0⟩ [fm]⊢⁺
    ⟨0, 0, (m + 1) + (2 * m + 2 * p + 6) + 5, 2 * (m + 1) + (2 * m + 2 * p + 6) + 5, 0⟩
  have h := main_trans m p
  convert h using 2; (ring_nf)

end Sz22_2003_unofficial_943
