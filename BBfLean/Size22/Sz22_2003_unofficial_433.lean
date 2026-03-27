import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #433: [27/35, 1/363, 50/3, 11/5, 21/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  0  0 -2
 1 -1  2  0  0
 0  0 -1  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_433

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- Drain: k (R5, R2) pairs. Converts a and e into d.
theorem drain : ∀ k a d e, ⟨a+k, 0, 0, d, e+2*k⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- R3 chain when e = 0: converts b into a and c.
theorem r3_chain_0 : ∀ k a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a+k, (0 : ℕ), c+2*k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- R3 chain when e = 1: converts b into a and c.
theorem r3_chain_1 : ∀ k a c, ⟨a, k, c, 0, 1⟩ [fm]⊢* ⟨a+k, (0 : ℕ), c+2*k, 0, 1⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase 2 round for e=0: R1, R1, R3 reducing d by 2.
theorem phase2_round_0 : ∀ k A B D,
    ⟨A, B, 2, D+2*k, 0⟩ [fm]⊢* ⟨A+k, B+5*k, (2 : ℕ), D, 0⟩ := by
  intro k; induction k with
  | zero => intro A B D; exists 0
  | succ k ih =>
    intro A B D
    rw [show D + 2 * (k + 1) = (D + 2 * k) + 1 + 1 from by ring]
    -- R1: c=2, d≥1
    step fm
    rw [show D + 2 * k + 1 = (D + 2 * k) + 1 from by ring]
    -- R1: c=1, d≥1
    step fm
    rw [show B + 3 + 3 = B + 6 from by ring]
    -- R3: b=B+6≥1, e=0<2
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- Phase 2 round for e=1: R1, R1, R3 reducing d by 2.
theorem phase2_round_1 : ∀ k A B D,
    ⟨A, B, 2, D+2*k, 1⟩ [fm]⊢* ⟨A+k, B+5*k, (2 : ℕ), D, 1⟩ := by
  intro k; induction k with
  | zero => intro A B D; exists 0
  | succ k ih =>
    intro A B D
    rw [show D + 2 * (k + 1) = (D + 2 * k) + 1 + 1 from by ring]
    step fm
    rw [show D + 2 * k + 1 = (D + 2 * k) + 1 from by ring]
    step fm
    rw [show B + 3 + 3 = B + 6 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- c_to_e: converts c into e (R4 repeated).
theorem c_to_e : ∀ k a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, (0 : ℕ), 0, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e
    rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- Phase 2 for even D (D = 2K), e=0:
-- (A, 0, 2, 2*K, 0) ⊢* (A+6*K, 0, 10*K+2, 0, 0)
theorem phase2_even_0 : ∀ K A,
    ⟨A, 0, 2, 2*K, 0⟩ [fm]⊢* ⟨A+6*K, (0 : ℕ), 10*K+2, 0, 0⟩ := by
  intro K A
  apply stepStar_trans (c₂ := ⟨A + K, 5 * K, 2, 0, 0⟩)
  · have h := phase2_round_0 K A 0 0
    simp only [Nat.zero_add] at h; exact h
  · have h := r3_chain_0 (5 * K) (A + K) 2
    rw [show A + K + 5 * K = A + 6 * K from by ring,
        show 2 + 2 * (5 * K) = 10 * K + 2 from by ring] at h
    exact h

-- Phase 2 for even D, e=1:
theorem phase2_even_1 : ∀ K A,
    ⟨A, 0, 2, 2*K, 1⟩ [fm]⊢* ⟨A+6*K, (0 : ℕ), 10*K+2, 0, 1⟩ := by
  intro K A
  apply stepStar_trans (c₂ := ⟨A + K, 5 * K, 2, 0, 1⟩)
  · have h := phase2_round_1 K A 0 0
    simp only [Nat.zero_add] at h; exact h
  · have h := r3_chain_1 (5 * K) (A + K) 2
    rw [show A + K + 5 * K = A + 6 * K from by ring,
        show 2 + 2 * (5 * K) = 10 * K + 2 from by ring] at h
    exact h

-- Phase 2 for odd D (D = 2K+1), e=0:
-- (A, 0, 2, 2*K+1, 0) ⊢* (A+6*K+3, 0, 10*K+7, 0, 0)
theorem phase2_odd_0 : ∀ K A,
    ⟨A, 0, 2, 2*K+1, 0⟩ [fm]⊢* ⟨A+6*K+3, (0 : ℕ), 10*K+7, 0, 0⟩ := by
  intro K A
  apply stepStar_trans (c₂ := ⟨A + K, 5 * K, 2, 1, 0⟩)
  · have h := phase2_round_0 K A 0 1
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * K = 2 * K + 1 from by ring] at h; exact h
  -- R1: (A+K, 5K, 2, 1, 0) -> (A+K, 5K+3, 1, 0, 0)
  step fm
  rw [show 5 * K + 3 = 5 * K + 3 from rfl]
  -- R3 chain
  apply stepStar_trans (c₂ := ⟨A + K + (5 * K + 3), 0, 1 + 2 * (5 * K + 3), 0, 0⟩)
  · exact r3_chain_0 (5 * K + 3) (A + K) 1
  · ring_nf; finish

-- Phase 2 for odd D, e=1:
theorem phase2_odd_1 : ∀ K A,
    ⟨A, 0, 2, 2*K+1, 1⟩ [fm]⊢* ⟨A+6*K+3, (0 : ℕ), 10*K+7, 0, 1⟩ := by
  intro K A
  apply stepStar_trans (c₂ := ⟨A + K, 5 * K, 2, 1, 1⟩)
  · have h := phase2_round_1 K A 0 1
    simp only [Nat.zero_add] at h
    rw [show 1 + 2 * K = 2 * K + 1 from by ring] at h; exact h
  -- R1: (A+K, 5K, 2, 1, 1) -> (A+K, 5K+3, 1, 0, 1)
  step fm
  rw [show 5 * K + 3 = 5 * K + 3 from rfl]
  apply stepStar_trans (c₂ := ⟨A + K + (5 * K + 3), 0, 1 + 2 * (5 * K + 3), 0, 1⟩)
  · exact r3_chain_1 (5 * K + 3) (A + K) 1
  · ring_nf; finish

-- Main transition for e even: from (f+1+a, 0, 0, 0, 2*f) to (3*f+4+a, 0, 0, 0, 5*f+7).
-- Here a represents the "excess" beyond f+1 in the first component.
theorem main_trans_even (f a : ℕ) :
    ⟨f+1+a, 0, 0, 0, 2*f⟩ [fm]⊢⁺ ⟨3*f+4+a, (0 : ℕ), 0, 0, 5*f+7⟩ := by
  -- drain f pairs: (f+1+a, 0, 0, 0, 2f) ⊢* (1+a, 0, 0, f, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1 + a, 0, 0, f, 0⟩)
  · have h := drain f (1 + a) 0 0
    simp only [Nat.zero_add] at h
    rw [show 1 + a + f = f + 1 + a from by ring] at h; exact h
  -- R5: (1+a, 0, 0, f, 0) -> (a, 1, 0, f+1, 0)
  apply step_stepStar_stepPlus (c₂ := ⟨a, 1, 0, f + 1, 0⟩)
  · rw [show 1 + a = a + 1 from by ring]; simp [fm]
  -- R3: (a, 1, 0, f+1, 0) -> (a+1, 0, 2, f+1, 0)
  apply stepStar_trans (c₂ := ⟨a + 1, 0, 2, f + 1, 0⟩)
  · rw [show (1 : ℕ) = 0 + 1 from rfl]; step fm; finish
  -- Phase 2: (a+1, 0, 2, f+1, 0) ⊢* (a+1+3*(f+1), 0, 5*(f+1)+2, 0, 0)
  apply stepStar_trans (c₂ := ⟨a + 1 + 3 * (f + 1), 0, 5 * (f + 1) + 2, 0, 0⟩)
  · rcases Nat.even_or_odd (f + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show f + 1 = 2 * K from by omega]
      have h := phase2_even_0 K (a + 1)
      rw [show a + 1 + 6 * K = a + 1 + 3 * (2 * K) from by ring,
          show 10 * K + 2 = 5 * (2 * K) + 2 from by ring] at h; exact h
    · rw [show f + 1 = 2 * K + 1 from by omega]
      have h := phase2_odd_0 K (a + 1)
      rw [show a + 1 + 6 * K + 3 = a + 1 + 3 * (2 * K + 1) from by ring,
          show 10 * K + 7 = 5 * (2 * K + 1) + 2 from by ring] at h; exact h
  -- c_to_e
  · have h := c_to_e (5 * (f + 1) + 2) (a + 1 + 3 * (f + 1)) 0
    simp only [Nat.zero_add] at h
    apply stepStar_trans h
    ring_nf; finish

-- Main transition for e odd: from (f+1+a, 0, 0, 0, 2*f+1) to (3*f+4+a, 0, 0, 0, 5*f+8).
theorem main_trans_odd (f a : ℕ) :
    ⟨f+1+a, 0, 0, 0, 2*f+1⟩ [fm]⊢⁺ ⟨3*f+4+a, (0 : ℕ), 0, 0, 5*f+8⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1 + a, 0, 0, f, 1⟩)
  · have h := drain f (1 + a) 0 1
    simp only [Nat.zero_add] at h
    rw [show 1 + a + f = f + 1 + a from by ring,
        show 1 + 2 * f = 2 * f + 1 from by ring] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨a, 1, 0, f + 1, 1⟩)
  · rw [show 1 + a = a + 1 from by ring]; simp [fm]
  apply stepStar_trans (c₂ := ⟨a + 1, 0, 2, f + 1, 1⟩)
  · rw [show (1 : ℕ) = 0 + 1 from rfl]; step fm; finish
  apply stepStar_trans (c₂ := ⟨a + 1 + 3 * (f + 1), 0, 5 * (f + 1) + 2, 0, 1⟩)
  · rcases Nat.even_or_odd (f + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show f + 1 = 2 * K from by omega]
      have h := phase2_even_1 K (a + 1)
      rw [show a + 1 + 6 * K = a + 1 + 3 * (2 * K) from by ring,
          show 10 * K + 2 = 5 * (2 * K) + 2 from by ring] at h; exact h
    · rw [show f + 1 = 2 * K + 1 from by omega]
      have h := phase2_odd_1 K (a + 1)
      rw [show a + 1 + 6 * K + 3 = a + 1 + 3 * (2 * K + 1) from by ring,
          show 10 * K + 7 = 5 * (2 * K + 1) + 2 from by ring] at h; exact h
  · have h := c_to_e (5 * (f + 1) + 2) (a + 1 + 3 * (f + 1)) 1
    apply stepStar_trans h
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 7⟩) (by execute fm 13)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨n + 2, 0, 0, 0, e⟩ ∧ e < 2 * (n + 2))
  · intro c ⟨nn, ee, hc, he⟩
    subst hc
    rcases Nat.even_or_odd ee with ⟨f, hf⟩ | ⟨f, hf⟩
    · -- e even: e = f + f
      have he' : f + f < 2 * (nn + 2) := hf ▸ he
      have hfn : f ≤ nn + 1 := by omega
      have h := main_trans_even f (nn + 1 - f)
      rw [show f + 1 + (nn + 1 - f) = nn + 2 from by omega,
          show 3 * f + 4 + (nn + 1 - f) = 2 * f + 5 + nn from by omega] at h
      have heq : (2 * f + 5 + nn, 0, 0, 0, 5 * f + 7) = (⟨2 * f + 3 + nn + 2, 0, 0, 0, 5 * f + 7⟩ : Q) := by
        congr 1; omega
      have hlt : 5 * f + 7 < 2 * (2 * f + 3 + nn + 2) := by
        suffices h : f < 2 * nn + 3 by omega
        omega
      refine ⟨⟨2 * f + 5 + nn, 0, 0, 0, 5 * f + 7⟩, ⟨2 * f + 3 + nn, 5 * f + 7, heq, hlt⟩, ?_⟩
      rw [hf, show f + f = 2 * f from by ring]; exact h
    · -- e odd: ee = 2*f + 1
      subst hf
      have hfn : f ≤ nn + 1 := by omega
      have h := main_trans_odd f (nn + 1 - f)
      rw [show f + 1 + (nn + 1 - f) = nn + 2 from by omega,
          show 3 * f + 4 + (nn + 1 - f) = 2 * f + 5 + nn from by omega] at h
      have heq : (2 * f + 5 + nn, 0, 0, 0, 5 * f + 8) = (⟨2 * f + 3 + nn + 2, 0, 0, 0, 5 * f + 8⟩ : Q) := by
        congr 1; omega
      have hlt : 5 * f + 8 < 2 * (2 * f + 3 + nn + 2) := by
        suffices hh : f < 2 * nn + 2 by omega
        omega
      refine ⟨⟨2 * f + 5 + nn, 0, 0, 0, 5 * f + 8⟩, ⟨2 * f + 3 + nn, 5 * f + 8, heq, hlt⟩, ?_⟩
      exact h
  · exact ⟨2, 7, rfl, by omega⟩

end Sz22_2003_unofficial_433
