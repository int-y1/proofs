import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #139: [9/35, 25/33, 22/5, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  2  0 -1
 1  0 -1  0  1
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_139

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- r3_chain: c → a+e
theorem r3_chain : ∀ k, ∀ a c e, ⟨a, 0, c+k, 0, e⟩ [fm]⊢* ⟨a+k, 0, c, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- r4_chain: e → d
theorem r4_chain : ∀ k, ∀ a d e, ⟨a, 0, 0, d, e+k⟩ [fm]⊢* ⟨a, 0, 0, d+k, e⟩ := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- r3r2_chain: each round R3 then R2, consumes 1 b, adds 1 to a and c
theorem r3r2_chain : ∀ k, ∀ a b c, ⟨a, b+k, c+1, 0, 0⟩ [fm]⊢* ⟨a+k, b, c+1+k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b c; exists 0
  | succ k ih =>
    intro a b c
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + 1 = (c + 0) + 1 from by ring]
    step fm
    rw [show c + 0 = c from by ring]
    step fm
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- d_drain_step: 5 steps consume 3 from d, add 5 to b
theorem d_drain_step : ∀ a b d, ⟨a+1, b, 0, d+3, 0⟩ [fm]⊢* ⟨a, b+5, 0, d, 0⟩ := by
  intro a b d
  rw [show d + 3 = (d + 2) + 1 from by ring]
  step fm
  step fm
  step fm
  rw [show d + 2 = (d + 1) + 1 from by ring]
  step fm
  rw [show d + 1 = d + 1 from rfl]
  step fm
  ring_nf; finish

-- d_drain_chain: k rounds
theorem d_drain_chain : ∀ k, ∀ a b, ⟨a+k, b, 0, 3*k, 0⟩ [fm]⊢* ⟨a, b+5*k, 0, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a b; exists 0
  | succ k ih =>
    intro a b
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 3 * (k + 1) = 3 * k + 3 from by ring]
    apply stepStar_trans (d_drain_step _ _ _)
    apply stepStar_trans (ih _ _)
    ring_nf; finish

-- d_drain_rem: drains 3*k from d, leaving remainder r
theorem d_drain_rem : ∀ k, ∀ a b r, ⟨a+k, b, 0, r + 3*k, 0⟩ [fm]⊢* ⟨a, b+5*k, 0, r, 0⟩ := by
  intro k; induction k with
  | zero => intro a b r; exists 0
  | succ k ih =>
    intro a b r
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show r + 3 * (k + 1) = (r + 3 * k) + 3 from by ring]
    apply stepStar_trans (d_drain_step _ _ _)
    apply stepStar_trans (ih _ _ _)
    ring_nf; finish

-- rem0: remainder 0 tail
theorem rem0 : ∀ A B, ⟨A+1, B+1, 0, 0, 0⟩ [fm]⊢* ⟨A+B, 0, B+3, 0, 0⟩ := by
  intro A B
  step fm
  step fm
  have h := r3r2_chain B A 0 2
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- rem1: remainder 1 tail
theorem rem1 : ∀ A B, ⟨A+1, B, 0, 1, 0⟩ [fm]⊢* ⟨A+B+1, 0, B+3, 0, 0⟩ := by
  intro A B
  step fm
  step fm
  step fm
  have h := r3r2_chain (B+1) A 0 1
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- rem2: remainder 2 tail
theorem rem2 : ∀ A B, ⟨A+1, B, 0, 2, 0⟩ [fm]⊢* ⟨A+B+3, 0, B+4, 0, 0⟩ := by
  intro A B
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring]
  step fm
  step fm
  step fm
  step fm
  step fm
  step fm
  have h := r3r2_chain (B+2) (A+1) 0 1
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- trans_mod1: c ≡ 1 (mod 3)
theorem trans_mod1 : ∀ k, ∀ a, ⟨a, 0, 3*k+1, 0, 0⟩ [fm]⊢⁺ ⟨a+7*k+1, 0, 5*k+3, 0, 0⟩ := by
  intro k a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+(3*k+1), 0, 0, 0, 3*k+1⟩)
  · have h := r3_chain (3*k+1) a 0 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨a+(3*k+1), 0, 0, 1, 3*k⟩)
  · show fm ⟨a + (3 * k + 1), 0, 0, 0, 3 * k + 1⟩ = some ⟨a + (3 * k + 1), 0, 0, 1, 3 * k⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨a+(3*k+1), 0, 0, 3*k+1, 0⟩)
  · have h := r4_chain (3*k) (a+(3*k+1)) 1 0
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨a+2*k+1, 5*k, 0, 1, 0⟩)
  · have h := d_drain_rem k (a+2*k+1) 0 1
    simp only [Nat.zero_add] at h
    rw [show a + (3 * k + 1) = (a + 2 * k + 1) + k from by ring,
        show 3 * k + 1 = 1 + 3 * k from by ring]
    exact h
  rw [show a + 2 * k + 1 = (a + 2 * k) + 1 from by ring]
  apply stepStar_trans (rem1 (a + 2 * k) (5 * k))
  ring_nf; finish

-- trans_mod2: c ≡ 2 (mod 3)
theorem trans_mod2 : ∀ k, ∀ a, ⟨a, 0, 3*k+2, 0, 0⟩ [fm]⊢⁺ ⟨a+7*k+4, 0, 5*k+4, 0, 0⟩ := by
  intro k a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+(3*k+2), 0, 0, 0, 3*k+2⟩)
  · have h := r3_chain (3*k+2) a 0 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨a+(3*k+2), 0, 0, 1, 3*k+1⟩)
  · show fm ⟨a + (3 * k + 2), 0, 0, 0, 3 * k + 2⟩ = some ⟨a + (3 * k + 2), 0, 0, 1, 3 * k + 1⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨a+(3*k+2), 0, 0, 3*k+2, 0⟩)
  · have h := r4_chain (3*k+1) (a+(3*k+2)) 1 0
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨a+2*k+2, 5*k, 0, 2, 0⟩)
  · have h := d_drain_rem k (a+2*k+2) 0 2
    simp only [Nat.zero_add] at h
    rw [show a + (3 * k + 2) = (a + 2 * k + 2) + k from by ring,
        show 3 * k + 2 = 2 + 3 * k from by ring]
    exact h
  rw [show a + 2 * k + 2 = (a + 2 * k + 1) + 1 from by ring]
  apply stepStar_trans (rem2 (a + 2 * k + 1) (5 * k))
  ring_nf; finish

-- trans_mod0: c ≡ 0 (mod 3), c ≥ 3
theorem trans_mod0 : ∀ k, ∀ a, ⟨a, 0, 3*(k+1), 0, 0⟩ [fm]⊢⁺ ⟨a+7*k+5, 0, 5*k+7, 0, 0⟩ := by
  intro k a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+3*(k+1), 0, 0, 0, 3*(k+1)⟩)
  · have h := r3_chain (3*(k+1)) a 0 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨a+3*(k+1), 0, 0, 1, 3*k+2⟩)
  · show fm ⟨a + 3 * (k + 1), 0, 0, 0, 3 * (k + 1)⟩ = some ⟨a + 3 * (k + 1), 0, 0, 1, 3 * k + 2⟩
    simp [fm]
  apply stepStar_trans (c₂ := ⟨a+3*(k+1), 0, 0, 3*(k+1), 0⟩)
  · have h := r4_chain (3*k+2) (a+3*(k+1)) 1 0
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨a+2*k+2, 5*(k+1), 0, 0, 0⟩)
  · have h := d_drain_chain (k+1) (a+2*k+2) 0
    simp only [Nat.zero_add] at h
    rw [show a + 3 * (k + 1) = (a + 2 * k + 2) + (k + 1) from by ring]
    exact h
  rw [show a + 2 * k + 2 = (a + 2 * k + 1) + 1 from by ring,
      show 5 * (k + 1) = (5 * k + 4) + 1 from by ring]
  apply stepStar_trans (rem0 (a + 2 * k + 1) (5 * k + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 4, 0, 0⟩) (by execute fm 14)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c, 0, 0⟩ ∧ c ≥ 1)
  · intro q ⟨a, c, hq, hc⟩; subst hq
    rcases (show c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 from by omega) with h0 | h1 | h2
    · obtain ⟨k, rfl⟩ : ∃ k, c = 3 * (k + 1) := ⟨c / 3 - 1, by omega⟩
      exact ⟨_, ⟨a + 7 * k + 5, 5 * k + 7, rfl, by omega⟩, trans_mod0 k a⟩
    · obtain ⟨k, rfl⟩ : ∃ k, c = 3 * k + 1 := ⟨c / 3, by omega⟩
      exact ⟨_, ⟨a + 7 * k + 1, 5 * k + 3, rfl, by omega⟩, trans_mod1 k a⟩
    · obtain ⟨k, rfl⟩ : ∃ k, c = 3 * k + 2 := ⟨c / 3, by omega⟩
      exact ⟨_, ⟨a + 7 * k + 4, 5 * k + 4, rfl, by omega⟩, trans_mod2 k a⟩
  · exact ⟨3, 4, rfl, by omega⟩

end Sz21_140_unofficial_139
