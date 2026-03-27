import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #126: [1/45, 10/77, 686/5, 3/7, 55/2]

Vector representation:
```
 0 -2 -1  0  0
 1  0  1 -1 -1
 1  0 -1  3  0
 0  1  0 -1  0
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_126

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+3, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 chain: d → b (when c=0, e=0)
theorem d_to_b : ∀ k a b d, ⟨a, b, 0, d+k, 0⟩ [fm]⊢* ⟨a, b+k, (0 : ℕ), d, (0 : ℕ)⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R5/R1 drain: interleaved a,b → e
theorem drain : ∀ k a b e, ⟨a+k, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a, b, (0 : ℕ), (0 : ℕ), e+k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring]
    step fm -- R5
    rw [show b + 2 * k + 1 + 1 = (b + 2 * k) + 1 + 1 from by ring]
    step fm -- R1
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R3 chain when b=0, e=0: c → d
theorem r3_chain_b0 : ∀ k a c d, ⟨a, 0, c+k, d, 0⟩ [fm]⊢* ⟨a+k, (0 : ℕ), c, d+3*k, (0 : ℕ)⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm -- R3
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R3 chain when b=1, e=0: c → d
theorem r3_chain_b1 : ∀ k a c d, ⟨a, 1, c+k, d, 0⟩ [fm]⊢* ⟨a+k, (1 : ℕ), c, d+3*k, (0 : ℕ)⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm -- R3
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R2/R3 interleaving for b=0: (a, 0, c, 3, k) →* (a+c+2k, 0, 0, 3(c+1)+2k, 0)
theorem r2r3_b0 : ∀ k a c, ⟨a, 0, c, 3, k⟩ [fm]⊢* ⟨a+c+2*k, (0 : ℕ), (0 : ℕ), 3*(c+1)+2*k, (0 : ℕ)⟩ := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k IH => match k with
    | 0 =>
      intro a c
      have h := r3_chain_b0 c a 0 3
      simp only [Nat.zero_add] at h
      rw [show a + c + 2 * 0 = a + c from by ring,
          show 3 * (c + 1) + 2 * 0 = 3 + 3 * c from by ring]
      exact h
    | 1 =>
      intro a c
      -- R2: (a, 0, c, 3, 1) → (a+1, 0, c+1, 2, 0)
      step fm
      -- R3 chain on c+1 with d=2
      have h := r3_chain_b0 (c+1) (a+1) 0 2
      simp only [Nat.zero_add] at h
      rw [show a + c + 2 * 1 = a + 1 + (c + 1) from by ring,
          show 3 * (c + 1) + 2 * 1 = 2 + 3 * (c + 1) from by ring]
      exact h
    | 2 =>
      intro a c
      -- R2x2: (a, 0, c, 3, 2) → (a+1, 0, c+1, 2, 1) → (a+2, 0, c+2, 1, 0)
      step fm; step fm
      -- R3 chain on c+2 with d=1
      have h := r3_chain_b0 (c+2) (a+2) 0 1
      simp only [Nat.zero_add] at h
      rw [show a + c + 2 * 2 = a + 2 + (c + 2) from by ring,
          show 3 * (c + 1) + 2 * 2 = 1 + 3 * (c + 2) from by ring]
      exact h
    | k+3 =>
      intro a c
      -- R2x3: (a, 0, c, 3, k+3) → ... → (a+3, 0, c+3, 0, k)
      step fm; step fm; step fm
      -- R3: (a+3, 0, c+3, 0, k) → (a+4, 0, c+2, 3, k)
      step fm
      -- IH with k (< k+3), c' = c+2
      apply stepStar_trans (IH k (by omega) (a+4) (c+2))
      ring_nf; finish

-- R2/R3 interleaving for b=1: (a, 1, c, 3, k) →* (a+c+2k, 1, 0, 3(c+1)+2k, 0)
theorem r2r3_b1 : ∀ k a c, ⟨a, 1, c, 3, k⟩ [fm]⊢* ⟨a+c+2*k, (1 : ℕ), (0 : ℕ), 3*(c+1)+2*k, (0 : ℕ)⟩ := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k IH => match k with
    | 0 =>
      intro a c
      have h := r3_chain_b1 c a 0 3
      simp only [Nat.zero_add] at h
      rw [show a + c + 2 * 0 = a + c from by ring,
          show 3 * (c + 1) + 2 * 0 = 3 + 3 * c from by ring]
      exact h
    | 1 =>
      intro a c
      step fm
      have h := r3_chain_b1 (c+1) (a+1) 0 2
      simp only [Nat.zero_add] at h
      rw [show a + c + 2 * 1 = a + 1 + (c + 1) from by ring,
          show 3 * (c + 1) + 2 * 1 = 2 + 3 * (c + 1) from by ring]
      exact h
    | 2 =>
      intro a c
      step fm; step fm
      have h := r3_chain_b1 (c+2) (a+2) 0 1
      simp only [Nat.zero_add] at h
      rw [show a + c + 2 * 2 = a + 2 + (c + 2) from by ring,
          show 3 * (c + 1) + 2 * 2 = 1 + 3 * (c + 2) from by ring]
      exact h
    | k+3 =>
      intro a c
      step fm; step fm; step fm; step fm
      apply stepStar_trans (IH k (by omega) (a+4) (c+2))
      ring_nf; finish

-- Main transition: (a+1, 0, 0, 0, e+1) ⊢⁺ (a+2e+4, 0, 0, 0, e+6)
theorem main_trans (a e : ℕ) : ⟨a+1, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨a+2*e+4, (0 : ℕ), (0 : ℕ), (0 : ℕ), e+6⟩ := by
  -- Phase 1: R5: (a+1, 0, 0, 0, e+1) → (a, 0, 1, 0, e+2)
  apply step_stepStar_stepPlus (c₂ := ⟨a, 0, 1, 0, e+2⟩)
  · simp [fm]
  -- Phase 2: R3: (a, 0, 1, 0, e+2) → (a+1, 0, 0, 3, e+2)
  apply stepStar_trans (c₂ := ⟨a+1, 0, 0, 3, e+2⟩)
  · step fm; finish
  -- Phase 3: r2r3_b0: (a+1, 0, 0, 3, e+2) →* (a+2e+5, 0, 0, 2e+7, 0)
  apply stepStar_trans (c₂ := ⟨a+2*e+5, 0, 0, 2*e+7, 0⟩)
  · have h := r2r3_b0 (e+2) (a+1) 0
    simp only [Nat.zero_add] at h
    rw [show a + 1 + 0 + 2 * (e + 2) = a + 2 * e + 5 from by ring,
        show 3 * (0 + 1) + 2 * (e + 2) = 2 * e + 7 from by ring] at h
    exact h
  -- Phase 4: d_to_b: (a+2e+5, 0, 0, 2e+7, 0) →* (a+2e+5, 2e+7, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+2*e+5, 2*e+7, 0, 0, 0⟩)
  · have h := d_to_b (2*e+7) (a+2*e+5) 0 0
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 5: drain with k=e+3: (a+2e+5, 2e+7, 0, 0, 0) →* (a+e+2, 1, 0, 0, e+3)
  apply stepStar_trans (c₂ := ⟨a+e+2, 1, 0, 0, e+3⟩)
  · have h := drain (e+3) (a+e+2) 1 0
    rw [show a + e + 2 + (e + 3) = a + 2 * e + 5 from by ring,
        show 1 + 2 * (e + 3) = 2 * e + 7 from by ring] at h
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 6: R5: (a+e+2, 1, 0, 0, e+3) → (a+e+1, 1, 1, 0, e+4)
  apply stepStar_trans (c₂ := ⟨a+e+1, 1, 1, 0, e+4⟩)
  · rw [show a + e + 2 = (a + e + 1) + 1 from by ring]
    step fm
    rw [show e + 3 + 1 = e + 4 from by ring]
    finish
  -- Phase 7: R3: (a+e+1, 1, 1, 0, e+4) → (a+e+2, 1, 0, 3, e+4)
  apply stepStar_trans (c₂ := ⟨a+e+2, 1, 0, 3, e+4⟩)
  · step fm; finish
  -- Phase 8: r2r3_b1: (a+e+2, 1, 0, 3, e+4) →* (a+3e+10, 1, 0, 2e+11, 0)
  apply stepStar_trans (c₂ := ⟨a+3*e+10, 1, 0, 2*e+11, 0⟩)
  · have h := r2r3_b1 (e+4) (a+e+2) 0
    simp only [Nat.zero_add] at h
    rw [show a + e + 2 + 0 + 2 * (e + 4) = a + 3 * e + 10 from by ring,
        show 3 * (0 + 1) + 2 * (e + 4) = 2 * e + 11 from by ring] at h
    exact h
  -- Phase 9: d_to_b: (a+3e+10, 1, 0, 2e+11, 0) →* (a+3e+10, 2e+12, 0, 0, 0)
  apply stepStar_trans (c₂ := ⟨a+3*e+10, 2*e+12, 0, 0, 0⟩)
  · have h := d_to_b (2*e+11) (a+3*e+10) 1 0
    rw [show 1 + (2 * e + 11) = 2 * e + 12 from by ring] at h
    simp only [Nat.zero_add] at h
    exact h
  -- Phase 10: drain with k=e+6: (a+3e+10, 2e+12, 0, 0, 0) →* (a+2e+4, 0, 0, 0, e+6)
  · have h := drain (e+6) (a+2*e+4) 0 0
    rw [show a + 2 * e + 4 + (e + 6) = a + 3 * e + 10 from by ring,
        show 0 + 2 * (e + 6) = 2 * e + 12 from by ring] at h
    simp only [Nat.zero_add] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 5⟩) (by execute fm 40)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a+1, 0, 0, 0, e+1⟩) ⟨1, 4⟩
  intro ⟨a, e⟩
  refine ⟨⟨a+2*e+3, e+5⟩, ?_⟩
  show ⟨a+1, 0, 0, 0, e+1⟩ [fm]⊢⁺ ⟨a+2*e+3+1, 0, 0, 0, e+5+1⟩
  rw [show a + 2 * e + 3 + 1 = a + 2 * e + 4 from by ring,
      show e + 5 + 1 = e + 6 from by ring]
  exact main_trans a e

end Sz22_2003_unofficial_126
