import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #64: [1/15, 98/3, 9/77, 5/7, 99/2]

Vector representation:
```
 0 -1 -1  0  0
 1 -1  0  2  0
 0  2  0 -1 -1
 0  0  1 -1  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_64

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

theorem r3r2r2_chain : ∀ k, ∀ a d e,
    (⟨a, 0, 0, d + 1, e + k⟩ : Q) [fm]⊢* ⟨a + 2*k, 0, 0, d + 3*k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (a + 2) (d + 3) e)
  ring_nf; finish

theorem r4_chain : ∀ k, ∀ a c d,
    (⟨a, 0, c, d + k, 0⟩ : Q) [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih a (c + 1) d)
  ring_nf; finish

theorem drain_even : ∀ k, ∀ a e,
    (⟨a + k, 0, 2*k, 0, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show 2 * (k + 1) = 2 * k + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

theorem drain_odd : ∀ k, ∀ a e,
    (⟨a + k + 1, 0, 2*k + 1, 0, e⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, 2, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · step fm; step fm; step fm; finish
  rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

theorem trans_d0_odd (a m : ℕ) :
    (⟨a + 1, 0, 0, 0, 2*m + 1⟩ : Q) [fm]⊢⁺ ⟨a + m + 1, 0, 0, 0, 3*m + 5⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 2*m + 1⟩ = some ⟨a, 2, 0, 0, 2*m + 2⟩; simp [fm]
  step fm; step fm
  apply stepStar_trans
  · have h := r3r2r2_chain (2*m + 2) (a + 2) 3 0
    rw [show 0 + (2 * m + 2) = 2 * m + 2 from by ring,
        show a + 2 + 2 * (2 * m + 2) = a + 4 * m + 6 from by ring,
        show 3 + 3 * (2 * m + 2) + 1 = 6 * m + 10 from by ring] at h; exact h
  apply stepStar_trans
  · have h := r4_chain (6*m + 10) (a + 4*m + 6) 0 0
    simp only [Nat.zero_add] at h; exact h
  have h := drain_even (3*m + 5) (a + m + 1) 0
  rw [show a + m + 1 + (3 * m + 5) = a + 4 * m + 6 from by ring,
      show 2 * (3 * m + 5) = 6 * m + 10 from by ring] at h
  simp only [Nat.zero_add] at h; exact h

theorem trans_d0_even (a m : ℕ) :
    (⟨a + 1, 0, 0, 0, 2*m + 2⟩ : Q) [fm]⊢⁺ ⟨a + m + 2, 0, 0, 2, 3*m + 7⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 2*m + 2⟩ = some ⟨a, 2, 0, 0, 2*m + 3⟩; simp [fm]
  step fm; step fm
  apply stepStar_trans
  · have h := r3r2r2_chain (2*m + 3) (a + 2) 3 0
    rw [show 0 + (2 * m + 3) = 2 * m + 3 from by ring,
        show a + 2 + 2 * (2 * m + 3) = a + 4 * m + 8 from by ring,
        show 3 + 3 * (2 * m + 3) + 1 = 6 * m + 13 from by ring] at h; exact h
  apply stepStar_trans
  · have h := r4_chain (6*m + 13) (a + 4*m + 8) 0 0
    simp only [Nat.zero_add] at h; exact h
  have h := drain_odd (3*m + 6) (a + m + 1) 0
  rw [show a + m + 1 + (3 * m + 6) + 1 = a + 4 * m + 8 from by ring,
      show 2 * (3 * m + 6) + 1 = 6 * m + 13 from by ring,
      show a + m + 1 + 1 = a + m + 2 from by ring,
      show 0 + (3 * m + 6) + 1 = 3 * m + 7 from by ring] at h; exact h

theorem trans_d2_even (a m : ℕ) :
    (⟨a + 1, 0, 0, 2, 2*m + 2⟩ : Q) [fm]⊢⁺ ⟨a + m + 1, 0, 0, 0, 3*m + 4⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring, show 2*m + 2 = (2*m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 1 + 1, (2*m + 1) + 1⟩ = some ⟨a + 1, 2, 0, 1, 2*m + 1⟩; simp [fm]
  step fm; step fm
  apply stepStar_trans
  · have h := r3r2r2_chain (2*m + 1) (a + 3) 4 0
    rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring,
        show a + 3 + 2 * (2 * m + 1) = a + 4 * m + 5 from by ring,
        show 4 + 3 * (2 * m + 1) + 1 = 6 * m + 8 from by ring] at h; exact h
  apply stepStar_trans
  · have h := r4_chain (6*m + 8) (a + 4*m + 5) 0 0
    simp only [Nat.zero_add] at h; exact h
  have h := drain_even (3*m + 4) (a + m + 1) 0
  rw [show a + m + 1 + (3 * m + 4) = a + 4 * m + 5 from by ring,
      show 2 * (3 * m + 4) = 6 * m + 8 from by ring] at h
  simp only [Nat.zero_add] at h; exact h

theorem trans_d2_odd (a m : ℕ) :
    (⟨a + 1, 0, 0, 2, 2*m + 1⟩ : Q) [fm]⊢⁺ ⟨a + m + 1, 0, 0, 2, 3*m + 3⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 1 + 1, 2*m + 1⟩ = some ⟨a + 1, 2, 0, 1, 2*m⟩; simp [fm]
  step fm; step fm
  apply stepStar_trans
  · have h := r3r2r2_chain (2*m) (a + 3) 4 0
    rw [show 0 + 2 * m = 2 * m from by ring,
        show a + 3 + 2 * (2 * m) = a + 4 * m + 3 from by ring,
        show 4 + 3 * (2 * m) + 1 = 6 * m + 5 from by ring] at h; exact h
  apply stepStar_trans
  · have h := r4_chain (6*m + 5) (a + 4*m + 3) 0 0
    simp only [Nat.zero_add] at h; exact h
  have h := drain_odd (3*m + 2) (a + m) 0
  rw [show a + m + (3 * m + 2) + 1 = a + 4 * m + 3 from by ring,
      show 2 * (3 * m + 2) + 1 = 6 * m + 5 from by ring,
      show a + m + 1 = a + m + 1 from by ring,
      show 0 + (3 * m + 2) + 1 = 3 * m + 3 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 7⟩) (by execute fm 72)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ (∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1 ∧ e ≥ 1) ∨
                   (∃ a e, q = ⟨a, 0, 0, 2, e⟩ ∧ a ≥ 1 ∧ e ≥ 1))
  · intro c hP
    rcases hP with ⟨a, e, hq, ha, he⟩ | ⟨a, e, hq, ha, he⟩
    · subst hq
      rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
      · have hK_pos : K ≥ 1 := by omega
        rw [show e = 2 * (K - 1) + 2 from by omega,
            show a = (a - 1) + 1 from by omega]
        exact ⟨_, Or.inr ⟨a - 1 + (K - 1) + 2, 3*(K - 1) + 7, rfl, by omega, by omega⟩,
               trans_d0_even (a - 1) (K - 1)⟩
      · rw [show e = 2 * K + 1 from by omega,
            show a = (a - 1) + 1 from by omega]
        exact ⟨_, Or.inl ⟨a - 1 + K + 1, 3*K + 5, rfl, by omega, by omega⟩,
               trans_d0_odd (a - 1) K⟩
    · subst hq
      rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
      · have hK_pos : K ≥ 1 := by omega
        rw [show e = 2 * (K - 1) + 2 from by omega,
            show a = (a - 1) + 1 from by omega]
        exact ⟨_, Or.inl ⟨a - 1 + (K - 1) + 1, 3*(K - 1) + 4, rfl, by omega, by omega⟩,
               trans_d2_even (a - 1) (K - 1)⟩
      · rw [show e = 2 * K + 1 from by omega,
            show a = (a - 1) + 1 from by omega]
        exact ⟨_, Or.inr ⟨a - 1 + K + 1, 3*K + 3, rfl, by omega, by omega⟩,
               trans_d2_odd (a - 1) K⟩
  · left; exact ⟨2, 7, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_64
