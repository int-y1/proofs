import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #137: [1/45, 196/15, 3/7, 25/2, 7/5]

Vector representation:
```
 0 -2 -1  0
 2 -1 -1  2
 0  1  0 -1
-1  0  2  0
 0  0 -1  1
```

This Fractran program doesn't halt. Starting from (1,0,0,0), computation
reaches (0, 0, 9, 0) in 28 steps and then loops through canonical states
(0, 0, 2n+3, 0). For even n=2m, (0,0,4m+3,0) ⊢⁺ (0,0,14m+9,0); for
odd n=2m+1, (0,0,4m+5,0) ⊢⁺ (0,0,14m+21,0).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_137

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

-- R3+R2 chain: each pair does R3 then R2
-- (a, 0, c+k, d+1) →* (a+2*k, 0, c, d+1+k)
theorem r3r2_chain : ∀ k a c d, ⟨a, 0, c+k, d+1⟩ [fm]⊢* ⟨a+2*k, (0 : ℕ), c, d+1+k⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm  -- R3
    step fm  -- R2
    apply stepStar_trans (ih (a + 2) c (d + 1))
    ring_nf; finish

-- R3 chain: (a, b, 0, d+k) →* (a, b+k, 0, d)
theorem r3_chain : ∀ k a b d, ⟨a, b, 0, d+k⟩ [fm]⊢* ⟨a, b+k, (0 : ℕ), d⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R3
    apply stepStar_trans (ih a (b + 1) d)
    ring_nf; finish

-- R4 chain: (a+k, 0, c, 0) →* (a, 0, c+2*k, 0)
theorem r4_chain : ∀ k a c, ⟨a+k, 0, c, 0⟩ [fm]⊢* ⟨a, (0 : ℕ), c+2*k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm  -- R4
    apply stepStar_trans (ih a (c + 2))
    ring_nf; finish

-- R4+R1+R1 drain: (a+k, b+4*k, 0, 0) →* (a, b, 0, 0)
theorem r4r1r1_drain : ∀ k a b, ⟨a+k, b+4*k, 0, 0⟩ [fm]⊢* ⟨a, b, (0 : ℕ), 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 4 * (k + 1) = (b + 4 * k) + 1 + 1 + 1 + 1 from by ring]
    step fm  -- R4
    rw [show b + 4 * k + 1 + 1 + 1 = (b + 4 * k) + 1 + 1 + 1 from by ring]
    step fm  -- R1
    rw [show b + 4 * k + 1 + 1 = (b + 4 * k) + 1 + 1 from by ring]
    step fm  -- R1
    apply stepStar_trans (ih a b)
    ring_nf; finish

-- Pump phase: (0, 0, 2n+3, 0) ⊢⁺ (4n+4, 0, 0, 2n+3)
theorem pump (n : ℕ) : ⟨0, 0, 2*n+3, 0⟩ [fm]⊢⁺ ⟨4*n+4, (0 : ℕ), 0, 2*n+3⟩ := by
  rw [show (2 * n + 3) = (2 * n + 2) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (2 * n + 2) + 1, 0⟩ = some ⟨0, 0, 2 * n + 2, 0 + 1⟩; rfl
  apply stepStar_trans (c₂ := ⟨0, 1, 2 * n + 2, 0⟩)
  · rw [show (0 : ℕ) + 1 = 1 from by ring]; step fm; finish
  apply stepStar_trans (c₂ := ⟨2, 0, 2 * n + 1, 2⟩)
  · rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm; finish
  have h := r3r2_chain (2 * n + 1) 2 0 1
  simp only [Nat.zero_add] at h
  rw [show 2 + 2 * (2 * n + 1) = 4 * n + 4 from by ring,
      show 1 + 1 + (2 * n + 1) = 2 * n + 3 from by ring] at h
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  rw [show (2 * n + 2 + 1 : ℕ) = 2 * n + 3 from by ring]
  exact h

-- Full main transition for n even (N=n+1 is odd, N=2m+1):
-- (0, 0, 4m+3, 0) ⊢⁺ (0, 0, 14m+9, 0)
theorem main_even (m : ℕ) :
    ⟨0, 0, 4*m+3, 0⟩ [fm]⊢⁺ ⟨0, (0 : ℕ), 14*m+9, 0⟩ := by
  -- Pump
  apply stepPlus_stepStar_stepPlus
  · have h := pump (2 * m)
    rw [show 2 * (2 * m) + 3 = 4 * m + 3 from by ring,
        show 4 * (2 * m) + 4 = 8 * m + 4 from by ring] at h
    exact h
  -- R3 chain
  apply stepStar_trans (c₂ := ⟨8 * m + 4, 4 * m + 3, 0, 0⟩)
  · have h := r3_chain (4 * m + 3) (8 * m + 4) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R4+R1+R1 drain (m cycles)
  apply stepStar_trans (c₂ := ⟨7 * m + 4, 3, 0, 0⟩)
  · have h := r4r1r1_drain m (7 * m + 4) 3
    rw [show 7 * m + 4 + m = 8 * m + 4 from by ring,
        show 3 + 4 * m = 4 * m + 3 from by ring] at h
    exact h
  -- Tail: (7m+4, 3, 0, 0) → ... → (0, 0, 14m+9, 0)
  -- R4: (7m+3, 3, 2, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 3, 3, 2, 0⟩)
  · rw [show 7 * m + 4 = (7 * m + 3) + 1 from by ring]; step fm; finish
  -- R1 (b=3≥2, c=2≥1): (7m+3, 1, 1, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 3, 1, 1, 0⟩)
  · rw [show (3 : ℕ) = 1 + 1 + 1 from by ring]; step fm; finish
  -- R2 (b=1, c=1): (7m+5, 0, 0, 2)
  apply stepStar_trans (c₂ := ⟨7 * m + 5, 0, 0, 2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 7 * m + 3 + 2 = 7 * m + 5 from by ring]
    step fm; finish
  -- R3 chain (2 steps)
  apply stepStar_trans (c₂ := ⟨7 * m + 5, 2, 0, 0⟩)
  · have h := r3_chain 2 (7 * m + 5) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R4: (7m+4, 2, 2, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 4, 2, 2, 0⟩)
  · rw [show 7 * m + 5 = (7 * m + 4) + 1 from by ring]; step fm; finish
  -- R1 (b=2≥2, c=2≥1): (7m+4, 0, 1, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 4, 0, 1, 0⟩)
  · step fm; finish
  -- R4: (7m+3, 0, 3, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 3, 0, 3, 0⟩)
  · rw [show 7 * m + 4 = (7 * m + 3) + 1 from by ring]; step fm; finish
  -- R4 chain (7m+3 steps)
  have h := r4_chain (7 * m + 3) 0 3
  simp only [Nat.zero_add] at h
  rw [show 3 + 2 * (7 * m + 3) = 14 * m + 9 from by ring] at h
  exact h

-- Full main transition for n odd (N=n+1 is even, N=2(m+1)):
-- (0, 0, 4m+5, 0) ⊢⁺ (0, 0, 14m+21, 0)
theorem main_odd (m : ℕ) :
    ⟨0, 0, 4*m+5, 0⟩ [fm]⊢⁺ ⟨0, (0 : ℕ), 14*m+21, 0⟩ := by
  -- Pump
  apply stepPlus_stepStar_stepPlus
  · have h := pump (2 * m + 1)
    rw [show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
        show 4 * (2 * m + 1) + 4 = 8 * m + 8 from by ring] at h
    exact h
  -- R3 chain
  apply stepStar_trans (c₂ := ⟨8 * m + 8, 4 * m + 5, 0, 0⟩)
  · have h := r3_chain (4 * m + 5) (8 * m + 8) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R4+R1+R1 drain (m+1 cycles)
  apply stepStar_trans (c₂ := ⟨7 * m + 7, 1, 0, 0⟩)
  · have h := r4r1r1_drain (m + 1) (7 * m + 7) 1
    rw [show 7 * m + 7 + (m + 1) = 8 * m + 8 from by ring,
        show 1 + 4 * (m + 1) = 4 * m + 5 from by ring] at h
    exact h
  -- Tail: (7m+7, 1, 0, 0) → ... → (0, 0, 14m+21, 0)
  -- R4: (7m+6, 1, 2, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 6, 1, 2, 0⟩)
  · rw [show 7 * m + 7 = (7 * m + 6) + 1 from by ring]; step fm; finish
  -- R2 (b=1, c=2): (7m+8, 0, 1, 2)
  apply stepStar_trans (c₂ := ⟨7 * m + 8, 0, 1, 2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring,
        show 7 * m + 6 + 2 = 7 * m + 8 from by ring]
    step fm; finish
  -- R3: (7m+8, 1, 1, 1)
  apply stepStar_trans (c₂ := ⟨7 * m + 8, 1, 1, 1⟩)
  · rw [show (2 : ℕ) = 1 + 1 from by ring]; step fm; finish
  -- R2 (b=1, c=1): (7m+10, 0, 0, 3)
  apply stepStar_trans (c₂ := ⟨7 * m + 10, 0, 0, 3⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 7 * m + 8 + 2 = 7 * m + 10 from by ring]
    step fm; finish
  -- R3 chain (3 steps)
  apply stepStar_trans (c₂ := ⟨7 * m + 10, 3, 0, 0⟩)
  · have h := r3_chain 3 (7 * m + 10) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R4: (7m+9, 3, 2, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 9, 3, 2, 0⟩)
  · rw [show 7 * m + 10 = (7 * m + 9) + 1 from by ring]; step fm; finish
  -- R1 (b=3≥2, c=2≥1): (7m+9, 1, 1, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 9, 1, 1, 0⟩)
  · rw [show (3 : ℕ) = 1 + 1 + 1 from by ring]; step fm; finish
  -- R2 (b=1, c=1): (7m+11, 0, 0, 2)
  apply stepStar_trans (c₂ := ⟨7 * m + 11, 0, 0, 2⟩)
  · rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 7 * m + 9 + 2 = 7 * m + 11 from by ring]
    step fm; finish
  -- R3 chain (2 steps)
  apply stepStar_trans (c₂ := ⟨7 * m + 11, 2, 0, 0⟩)
  · have h := r3_chain 2 (7 * m + 11) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- R4: (7m+10, 2, 2, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 10, 2, 2, 0⟩)
  · rw [show 7 * m + 11 = (7 * m + 10) + 1 from by ring]; step fm; finish
  -- R1 (b=2≥2, c=2≥1): (7m+10, 0, 1, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 10, 0, 1, 0⟩)
  · step fm; finish
  -- R4: (7m+9, 0, 3, 0)
  apply stepStar_trans (c₂ := ⟨7 * m + 9, 0, 3, 0⟩)
  · rw [show 7 * m + 10 = (7 * m + 9) + 1 from by ring]; step fm; finish
  -- R4 chain (7m+9 steps)
  have h := r4_chain (7 * m + 9) 0 3
  simp only [Nat.zero_add] at h
  rw [show 3 + 2 * (7 * m + 9) = 14 * m + 21 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 9, 0⟩) (by execute fm 28)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 * n + 3, 0⟩) 3
  intro n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n even, n = 2m
    subst hm
    refine ⟨7 * m + 3, ?_⟩
    rw [show 2 * (m + m) + 3 = 4 * m + 3 from by ring,
        show 2 * (7 * m + 3) + 3 = 14 * m + 9 from by ring]
    exact main_even m
  · -- n odd, n = 2m+1
    subst hm
    refine ⟨7 * m + 9, ?_⟩
    rw [show 2 * (2 * m + 1) + 3 = 4 * m + 5 from by ring,
        show 2 * (7 * m + 9) + 3 = 14 * m + 21 from by ring]
    exact main_odd m

end Sz22_2003_unofficial_137
