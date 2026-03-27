import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #237: [11/105, 27/55, 10/3, 7/2, 55/7]

Vector representation:
```
 0 -1 -1 -1  1
 0  3 -1  0 -1
 1 -1  1  0  0
-1  0  0  1  0
 0  0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_237

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    step fm
    apply stepStar_trans (ih c (d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + k, 0, c + k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    step fm
    apply stepStar_trans (ih (a + 1) (c + 1))
    ring_nf; finish

theorem pump_e : ∀ k a b, ⟨a, b + 1, 0, 0, k⟩ [fm]⊢* ⟨a + k, b + 2 * k + 1, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b
    step fm
    step fm
    rw [show b + 3 = (b + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 2))
    ring_nf; finish

theorem pump_d : ∀ k a d e, ⟨a, 3, 0, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 3, 0, d, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = d + k + 1 from by ring]
    step fm
    step fm
    step fm
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem first_drain : ∀ c d, ⟨0, 0, c + 3, d + 4, 0⟩ [fm]⊢* ⟨0, 0, c, d, 3⟩ := by
  intro c d
  rw [show d + 4 = d + 3 + 1 from by ring]
  step fm
  step fm
  step fm
  step fm
  step fm
  finish

theorem drain_cycles : ∀ k c d e,
    ⟨0, 0, c + 4 * k, d + 3 * k, e + 1⟩ [fm]⊢* ⟨0, 0, c, d, e + 2 * k + 1⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + 4 * (k + 1) = c + 4 * k + 3 + 1 from by ring,
        show d + 3 * (k + 1) = d + 3 * k + 2 + 1 from by ring]
    step fm
    step fm
    step fm
    step fm
    rw [show e + 1 + 1 + 1 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih c d (e + 2))
    ring_nf; finish

theorem middle_even : ∀ d e, ⟨0, 0, 0, d + 1, e + 1⟩ [fm]⊢* ⟨0, 3, 0, d, e + 1⟩ := by
  intro d e
  step fm
  step fm
  finish

theorem middle_odd : ∀ d e, ⟨0, 0, 2, d + 2, e + 1⟩ [fm]⊢* ⟨0, 3, 0, d, e + 2⟩ := by
  intro d e
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  step fm
  step fm
  step fm
  step fm
  rw [show e + 2 = e + 1 + 1 from by ring]
  step fm
  step fm
  finish

theorem r3_r4_tail : ∀ a b c,
    ⟨a, b, c, 0, 0⟩ [fm]⊢* ⟨0, 0, c + b, a + b, 0⟩ := by
  intro a b c
  apply stepStar_trans (r3_chain b a c)
  have h := r4_chain (a + b) (c + b) 0
  rw [show (0 : ℕ) + (a + b) = a + b from by ring] at h
  exact h

theorem main_trans_even (m d : ℕ) :
    ⟨0, 0, 12 * m + 9, d + 9 * m + 9, 0⟩ [fm]⊢⁺ ⟨0, 0, 12 * m + 15, 2 * d + 18 * m + 21, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := first_drain (12 * m + 6) (d + 9 * m + 5)
    rw [show 12 * m + 6 + 3 = 12 * m + 9 from by ring,
        show d + 9 * m + 5 + 4 = d + 9 * m + 9 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := drain_cycles (3 * m + 1) 2 (d + 2) 2
    rw [show 2 + 4 * (3 * m + 1) = 12 * m + 6 from by ring,
        show d + 2 + 3 * (3 * m + 1) = d + 9 * m + 5 from by ring,
        show 2 + 1 = 3 from by ring,
        show 2 + 2 * (3 * m + 1) + 1 = 6 * m + 5 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := middle_odd d (6 * m + 4)
    rw [show 6 * m + 4 + 1 = 6 * m + 5 from by ring,
        show 6 * m + 4 + 2 = 6 * m + 6 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := pump_d d 0 0 (6 * m + 6)
    rw [show (0 : ℕ) + d = d from by ring,
        show 0 + 2 * d = 2 * d from by ring] at h; exact h
  -- State: (2d, 3, 0, 0, 6m+6). pump_e then r3_r4_tail.
  -- First step gives stepPlus
  step fm  -- R3: (2d+1, 2, 1, 0, 6m+6)
  step fm  -- R2: (2d+1, 5, 0, 0, 6m+5)
  rw [show (5 : ℕ) = (4 : ℕ) + 1 from by ring]
  apply stepStar_trans
  · have h := pump_e (6 * m + 5) (2 * d + 1) 4
    rw [show 2 * d + 1 + (6 * m + 5) = 2 * d + 6 * m + 6 from by ring,
        show 4 + 2 * (6 * m + 5) + 1 = 12 * m + 15 from by ring] at h; exact h
  have h := r3_r4_tail (2 * d + 6 * m + 6) (12 * m + 15) 0
  rw [show (0 : ℕ) + (12 * m + 15) = 12 * m + 15 from by ring,
      show 2 * d + 6 * m + 6 + (12 * m + 15) = 2 * d + 18 * m + 21 from by ring] at h
  exact h

theorem main_trans_odd (m d : ℕ) :
    ⟨0, 0, 12 * m + 15, d + 9 * m + 14, 0⟩ [fm]⊢⁺ ⟨0, 0, 12 * m + 21, 2 * d + 18 * m + 30, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · have h := first_drain (12 * m + 12) (d + 9 * m + 10)
    rw [show 12 * m + 12 + 3 = 12 * m + 15 from by ring,
        show d + 9 * m + 10 + 4 = d + 9 * m + 14 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := drain_cycles (3 * m + 3) 0 (d + 1) 2
    rw [show 0 + 4 * (3 * m + 3) = 12 * m + 12 from by ring,
        show d + 1 + 3 * (3 * m + 3) = d + 9 * m + 10 from by ring,
        show 2 + 1 = 3 from by ring,
        show 2 + 2 * (3 * m + 3) + 1 = 6 * m + 9 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := middle_even d (6 * m + 8)
    rw [show 6 * m + 8 + 1 = 6 * m + 9 from by ring] at h; exact h
  apply stepStar_stepPlus_stepPlus
  · have h := pump_d d 0 0 (6 * m + 9)
    rw [show (0 : ℕ) + d = d from by ring,
        show 0 + 2 * d = 2 * d from by ring] at h; exact h
  -- State: (2d, 3, 0, 0, 6m+9). pump_e then r3_r4_tail.
  step fm  -- R3: (2d+1, 2, 1, 0, 6m+9)
  step fm  -- R2: (2d+1, 5, 0, 0, 6m+8)
  rw [show (5 : ℕ) = (4 : ℕ) + 1 from by ring]
  apply stepStar_trans
  · have h := pump_e (6 * m + 8) (2 * d + 1) 4
    rw [show 2 * d + 1 + (6 * m + 8) = 2 * d + 6 * m + 9 from by ring,
        show 4 + 2 * (6 * m + 8) + 1 = 12 * m + 21 from by ring] at h; exact h
  have h := r3_r4_tail (2 * d + 6 * m + 9) (12 * m + 21) 0
  rw [show (0 : ℕ) + (12 * m + 21) = 12 * m + 21 from by ring,
      show 2 * d + 6 * m + 9 + (12 * m + 21) = 2 * d + 18 * m + 30 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 9, 15, 0⟩) (by execute fm 73)
  apply progress_nonhalt (fm := fm)
    (P := fun c ↦ (∃ m d, c = (⟨0, 0, 12 * m + 9, d + 9 * m + 9, 0⟩ : Q)) ∨
                   (∃ m d, c = (⟨0, 0, 12 * m + 15, d + 9 * m + 14, 0⟩ : Q)))
  · intro c hc
    rcases hc with ⟨m, d, hc⟩ | ⟨m, d, hc⟩
    · -- even family -> odd family
      exact ⟨⟨0, 0, 12 * m + 15, 2 * d + 18 * m + 21, 0⟩,
             Or.inr ⟨m, 2 * d + 9 * m + 7, by
               show (⟨0, 0, 12 * m + 15, 2 * d + 18 * m + 21, 0⟩ : Q) =
                    ⟨0, 0, 12 * m + 15, 2 * d + 9 * m + 7 + 9 * m + 14, 0⟩
               rw [show 2 * d + 9 * m + 7 + 9 * m + 14 = 2 * d + 18 * m + 21 from by ring]⟩,
             hc ▸ main_trans_even m d⟩
    · -- odd family -> even family
      exact ⟨⟨0, 0, 12 * (m + 1) + 9, 2 * d + 18 * m + 30, 0⟩,
             Or.inl ⟨m + 1, 2 * d + 9 * m + 12, by
               show (⟨0, 0, 12 * (m + 1) + 9, 2 * d + 18 * m + 30, 0⟩ : Q) =
                    ⟨0, 0, 12 * (m + 1) + 9, 2 * d + 9 * m + 12 + 9 * (m + 1) + 9, 0⟩
               rw [show 2 * d + 9 * m + 12 + 9 * (m + 1) + 9 = 2 * d + 18 * m + 30 from by ring]⟩,
             hc ▸ main_trans_odd m d⟩
  · exact Or.inl ⟨0, 6, rfl⟩

end Sz22_2003_unofficial_237
