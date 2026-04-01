import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1581: [7/45, 50/77, 11/5, 3/11, 245/2]

Vector representation:
```
 0 -2 -1  1  0
 1  0  2 -1 -1
 0  0 -1  0  1
 0  1  0  0 -1
-1  0  1  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1581

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | _ => none

theorem drain : ∀ k, ∀ a b d,
    ⟨a + k, b + 2 * k, (0 : ℕ), d, (0 : ℕ)⟩ [fm]⊢* ⟨a, b, 0, d + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; simp; exists 0
  | succ k ih =>
    intro a b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a b (d + 3))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem climb_b0 : ∀ k, ∀ a c d,
    ⟨a, (0 : ℕ), c + 1, d + k, (0 : ℕ)⟩ [fm]⊢* ⟨a + k, 0, c + k + 1, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (c + 1) d)
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem climb_b1 : ∀ k, ∀ a c d,
    ⟨a, (1 : ℕ), c + 1, d + k, (0 : ℕ)⟩ [fm]⊢* ⟨a + k, 1, c + k + 1, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (c + 1) d)
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem c_to_e_b0 : ∀ k, ∀ a e,
    ⟨a, (0 : ℕ), k, (0 : ℕ), e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e; step fm
    apply stepStar_trans (ih a (e + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem c_to_e_b1 : ∀ k, ∀ a e,
    ⟨a, (1 : ℕ), k, (0 : ℕ), e⟩ [fm]⊢* ⟨a, 1, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e; step fm
    apply stepStar_trans (ih a (e + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

theorem e_to_b : ∀ k, ∀ a b,
    ⟨a, b, (0 : ℕ), (0 : ℕ), k⟩ [fm]⊢* ⟨a, b + k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b; step fm
    apply stepStar_trans (ih a (b + 1))
    refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

-- Form 1, d=2j: (a+1, 0, 0, 2j+1, 0) ->+ (a+j+1, 0, 0, 3j+6, 0)
theorem trans_f1_de (a j : ℕ) :
    ⟨a + 1, (0 : ℕ), 0, 2 * j + 1, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a + j + 1, 0, 0, 3 * j + 6, 0⟩ := by
  step fm
  rw [show 2 * j + 1 + 2 = 0 + (2 * j + 3) from by ring]
  apply stepStar_trans (climb_b0 (2 * j + 3) a 0 0)
  rw [show a + (2 * j + 3) = a + 2 * j + 3 from by ring,
      show 0 + (2 * j + 3) + 1 = 2 * j + 4 from by ring]
  apply stepStar_trans (c_to_e_b0 (2 * j + 4) (a + 2 * j + 3) 0)
  rw [show 0 + (2 * j + 4) = 2 * j + 4 from by ring]
  apply stepStar_trans (e_to_b (2 * j + 4) (a + 2 * j + 3) 0)
  rw [show 0 + (2 * j + 4) = 0 + 2 * (j + 2) from by ring,
      show a + 2 * j + 3 = (a + j + 1) + (j + 2) from by ring]
  apply stepStar_trans (drain (j + 2) (a + j + 1) 0 0)
  refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

-- Form 1, d=2j+1: (a+1, 0, 0, 2j+2, 0) ->+ (a+j+2, 1, 0, 3j+6, 0)
theorem trans_f1_do (a j : ℕ) :
    ⟨a + 1, (0 : ℕ), 0, 2 * j + 2, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a + j + 2, 1, 0, 3 * j + 6, 0⟩ := by
  step fm
  rw [show 2 * j + 2 + 2 = 0 + (2 * j + 4) from by ring]
  apply stepStar_trans (climb_b0 (2 * j + 4) a 0 0)
  rw [show a + (2 * j + 4) = a + 2 * j + 4 from by ring,
      show 0 + (2 * j + 4) + 1 = 2 * j + 5 from by ring]
  apply stepStar_trans (c_to_e_b0 (2 * j + 5) (a + 2 * j + 4) 0)
  rw [show 0 + (2 * j + 5) = 2 * j + 5 from by ring]
  apply stepStar_trans (e_to_b (2 * j + 5) (a + 2 * j + 4) 0)
  rw [show 0 + (2 * j + 5) = 1 + 2 * (j + 2) from by ring,
      show a + 2 * j + 4 = (a + j + 2) + (j + 2) from by ring]
  apply stepStar_trans (drain (j + 2) (a + j + 2) 1 0)
  refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

-- Form 2, d=2j: (a+1, 1, 0, 2j+1, 0) ->+ (a+j+1, 1, 0, 3j+6, 0)
theorem trans_f2_de (a j : ℕ) :
    ⟨a + 1, (1 : ℕ), 0, 2 * j + 1, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a + j + 1, 1, 0, 3 * j + 6, 0⟩ := by
  step fm
  rw [show 2 * j + 1 + 2 = 0 + (2 * j + 3) from by ring]
  apply stepStar_trans (climb_b1 (2 * j + 3) a 0 0)
  rw [show a + (2 * j + 3) = a + 2 * j + 3 from by ring,
      show 0 + (2 * j + 3) + 1 = 2 * j + 4 from by ring]
  apply stepStar_trans (c_to_e_b1 (2 * j + 4) (a + 2 * j + 3) 0)
  rw [show 0 + (2 * j + 4) = 2 * j + 4 from by ring]
  apply stepStar_trans (e_to_b (2 * j + 4) (a + 2 * j + 3) 1)
  rw [show 1 + (2 * j + 4) = 1 + 2 * (j + 2) from by ring,
      show a + 2 * j + 3 = (a + j + 1) + (j + 2) from by ring]
  apply stepStar_trans (drain (j + 2) (a + j + 1) 1 0)
  refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

-- Form 2, d=2j+1: (a+1, 1, 0, 2j+2, 0) ->+ (a+j+1, 0, 0, 3j+9, 0)
-- D=2j+2 even, B=D+4=2j+6 even, drain j+3
theorem trans_f2_do (a j : ℕ) :
    ⟨a + 1, (1 : ℕ), 0, 2 * j + 2, (0 : ℕ)⟩ [fm]⊢⁺ ⟨a + j + 1, 0, 0, 3 * j + 9, 0⟩ := by
  step fm
  rw [show 2 * j + 2 + 2 = 0 + (2 * j + 4) from by ring]
  apply stepStar_trans (climb_b1 (2 * j + 4) a 0 0)
  rw [show a + (2 * j + 4) = a + 2 * j + 4 from by ring,
      show 0 + (2 * j + 4) + 1 = 2 * j + 5 from by ring]
  apply stepStar_trans (c_to_e_b1 (2 * j + 5) (a + 2 * j + 4) 0)
  rw [show 0 + (2 * j + 5) = 2 * j + 5 from by ring]
  apply stepStar_trans (e_to_b (2 * j + 5) (a + 2 * j + 4) 1)
  rw [show 1 + (2 * j + 5) = 0 + 2 * (j + 3) from by ring,
      show a + 2 * j + 4 = (a + j + 1) + (j + 3) from by ring]
  apply stepStar_trans (drain (j + 3) (a + j + 1) 0 0)
  refine ⟨0, ?_⟩; simp only [stepNat, Nat.repeat]; ring_nf

-- Main transition: combine all 4 cases
theorem main_trans :
    ∀ q, (∃ a d, q = ⟨a + 1, 0, 0, d + 1, 0⟩ ∨ q = ⟨a + 1, 1, 0, d + 1, 0⟩) →
    ∃ q', (∃ a d, q' = ⟨a + 1, 0, 0, d + 1, 0⟩ ∨ q' = ⟨a + 1, 1, 0, d + 1, 0⟩) ∧ q [fm]⊢⁺ q' := by
  intro q ⟨a, d, h⟩
  rcases h with h | h
  · -- Form 1: (a+1, 0, 0, d+1, 0)
    rcases Nat.even_or_odd d with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- d even, d = j+j
      subst hj; rw [show j + j + 1 = 2 * j + 1 from by ring] at h
      exact ⟨_, ⟨a + j, 3 * j + 5, Or.inl rfl⟩, h ▸ trans_f1_de a j⟩
    · -- d odd, d = 2*j+1
      subst hj; rw [show 2 * j + 1 + 1 = 2 * j + 2 from by ring] at h
      exact ⟨_, ⟨a + j + 1, 3 * j + 5, Or.inr rfl⟩, h ▸ trans_f1_do a j⟩
  · -- Form 2: (a+1, 1, 0, d+1, 0)
    rcases Nat.even_or_odd d with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- d even, d = j+j
      subst hj; rw [show j + j + 1 = 2 * j + 1 from by ring] at h
      exact ⟨_, ⟨a + j, 3 * j + 5, Or.inr rfl⟩, h ▸ trans_f2_de a j⟩
    · -- d odd, d = 2*j+1
      subst hj; rw [show 2 * j + 1 + 1 = 2 * j + 2 from by ring] at h
      exact ⟨_, ⟨a + j, 3 * j + 8, Or.inl rfl⟩, h ▸ trans_f2_do a j⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 1, 0, 3, 0⟩) (by execute fm 13)
  apply progress_nonhalt
    (P := fun q ↦ ∃ a d, q = ⟨a + 1, 0, 0, d + 1, 0⟩ ∨ q = ⟨a + 1, 1, 0, d + 1, 0⟩)
    main_trans ⟨0, 2, Or.inr rfl⟩

end Sz22_2003_unofficial_1581
