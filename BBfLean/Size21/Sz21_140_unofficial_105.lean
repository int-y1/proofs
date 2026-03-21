import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #105: [7/15, 3/847, 50/7, 11/5, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -2
 1  0  2 -1  0
 0  0 -1  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_105

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R5R2 chain (even e)
theorem r5r2_even' : ∀ m a b, ⟨a+m, b, 0, 0, 2*m⟩ [fm]⊢* ⟨a, b+2*m, 0, 0, 0⟩ := by
  intro m; induction' m with m ih <;> intro a b
  · exists 0
  rw [show a + (m + 1) = (a + m) + 1 from by ring,
      show 2 * (m + 1) = 2 * m + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a (b + 2))
  ring_nf; finish

-- R5R2 chain (odd e)
theorem r5r2_odd' : ∀ m a b, ⟨a+m, b, 0, 0, 2*m+1⟩ [fm]⊢* ⟨a, b+2*m, 0, 0, 1⟩ := by
  intro m; induction' m with m ih <;> intro a b
  · exists 0
  rw [show a + (m + 1) = (a + m) + 1 from by ring,
      show 2 * (m + 1) + 1 = 2 * m + 1 + 2 from by ring]
  step fm; step fm
  apply stepStar_trans (ih a (b + 2))
  ring_nf; finish

-- R3 chain (e=0)
theorem r3_chain_0 : ∀ d a c, ⟨a, 0, c, d, 0⟩ [fm]⊢* ⟨a+d, 0, c+2*d, 0, 0⟩ := by
  intro d; induction' d with d ih <;> intro a c
  · exists 0
  rw [show (d + 1 : ℕ) = d + 1 from rfl]
  step fm
  apply stepStar_trans (ih (a+1) (c+2))
  ring_nf; finish

-- R3 chain (e=1)
theorem r3_chain_1 : ∀ d a c, ⟨a, 0, c, d, 1⟩ [fm]⊢* ⟨a+d, 0, c+2*d, 0, 1⟩ := by
  intro d; induction' d with d ih <;> intro a c
  · exists 0
  rw [show (d + 1 : ℕ) = d + 1 from rfl]
  step fm
  apply stepStar_trans (ih (a+1) (c+2))
  ring_nf; finish

-- R4 chain: c → e
theorem c_to_e : ∀ c a e, ⟨a, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+c⟩ := by
  intro c; induction' c with c ih <;> intro a e
  · exists 0
  rw [show (c + 1 : ℕ) = c + 1 from rfl]
  step fm
  apply stepStar_trans (ih a (e + 1))
  ring_nf; finish

-- R3R1R1 chain (e=0)
theorem r3r1r1_0 : ∀ k a d, ⟨a, 2*k+1, 0, d+1, 0⟩ [fm]⊢* ⟨a+k, 1, 0, d+k+1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm; step fm
  rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
  apply stepStar_trans (ih (a + 1) (d + 1))
  ring_nf; finish

-- R3R1R1 chain (e=1)
theorem r3r1r1_1 : ∀ k a d, ⟨a, 2*k+1, 0, d+1, 1⟩ [fm]⊢* ⟨a+k, 1, 0, d+k+1, 1⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
  step fm; step fm; step fm
  rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
  apply stepStar_trans (ih (a + 1) (d + 1))
  ring_nf; finish

-- Even transition for m=0
theorem even_trans_0 : ∀ a, ⟨a+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+2, 0, 0, 0, 3⟩ := by
  intro a
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 0⟩ = some ⟨a, 1, 0, 1, 0⟩; simp [fm]
  step fm; step fm; step fm
  apply stepStar_trans (c_to_e 3 (a + 2) 0)
  ring_nf; finish

-- Even transition for m >= 1
theorem even_trans : ∀ m a, ⟨a+m+2, 0, 0, 0, 2*m+2⟩ [fm]⊢⁺ ⟨a+2*m+4, 0, 0, 0, 2*m+5⟩ := by
  intro m a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 1, 2 * m + 2, 0, 0, 0⟩)
  · rw [show a + m + 2 = (a + 1) + (m + 1) from by ring,
        show 2 * m + 2 = 2 * (m + 1) from by ring]
    have h := r5r2_even' (m + 1) (a + 1) 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨a, 2 * m + 3, 0, 1, 0⟩)
  · show fm ⟨a + 1, 2 * m + 2, 0, 0, 0⟩ = some ⟨a, 2 * m + 3, 0, 1, 0⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨a + 1, 2 * m + 1, 0, 2, 0⟩)
  · rw [show 2 * m + 3 = (2 * m + 1) + 2 from by ring]
    step fm; step fm; step fm; finish
  apply stepStar_trans (c₂ := ⟨a + m + 1, 1, 0, m + 2, 0⟩)
  · rw [show 2 = 1 + 1 from rfl]
    have h := r3r1r1_0 m (a + 1) 1
    rw [show a + 1 + m = a + m + 1 from by ring,
        show 1 + m + 1 = m + 2 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨a + m + 2, 0, 1, m + 2, 0⟩)
  · step fm; step fm; finish
  apply stepStar_trans (c₂ := ⟨a + 2 * m + 4, 0, 2 * m + 5, 0, 0⟩)
  · have h := r3_chain_0 (m + 2) (a + m + 2) 1
    rw [show a + m + 2 + (m + 2) = a + 2 * m + 4 from by ring,
        show 1 + 2 * (m + 2) = 2 * m + 5 from by ring] at h
    exact h
  have h := c_to_e (2 * m + 5) (a + 2 * m + 4) 0
  rw [show 0 + (2 * m + 5) = 2 * m + 5 from by ring] at h
  exact h

-- Odd transition for m >= 1
theorem odd_trans : ∀ m a, ⟨a+m+2, 0, 0, 0, 2*m+3⟩ [fm]⊢⁺ ⟨a+2*m+4, 0, 0, 0, 2*m+6⟩ := by
  intro m a
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a + 1, 2 * m + 2, 0, 0, 1⟩)
  · rw [show a + m + 2 = (a + 1) + (m + 1) from by ring,
        show 2 * m + 3 = 2 * (m + 1) + 1 from by ring]
    have h := r5r2_odd' (m + 1) (a + 1) 0
    simp only [Nat.zero_add] at h; exact h
  apply step_stepStar_stepPlus (c₂ := ⟨a, 2 * m + 3, 0, 1, 1⟩)
  · show fm ⟨a + 1, 2 * m + 2, 0, 0, 1⟩ = some ⟨a, 2 * m + 3, 0, 1, 1⟩; simp [fm]
  apply stepStar_trans (c₂ := ⟨a + 1, 2 * m + 1, 0, 2, 1⟩)
  · rw [show 2 * m + 3 = (2 * m + 1) + 2 from by ring]
    step fm; step fm; step fm; finish
  apply stepStar_trans (c₂ := ⟨a + m + 1, 1, 0, m + 2, 1⟩)
  · rw [show 2 = 1 + 1 from rfl]
    have h := r3r1r1_1 m (a + 1) 1
    rw [show a + 1 + m = a + m + 1 from by ring,
        show 1 + m + 1 = m + 2 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨a + m + 2, 0, 1, m + 2, 1⟩)
  · step fm; step fm; finish
  apply stepStar_trans (c₂ := ⟨a + 2 * m + 4, 0, 2 * m + 5, 0, 1⟩)
  · have h := r3_chain_1 (m + 2) (a + m + 2) 1
    rw [show a + m + 2 + (m + 2) = a + 2 * m + 4 from by ring,
        show 1 + 2 * (m + 2) = 2 * m + 5 from by ring] at h
    exact h
  have h := c_to_e (2 * m + 5) (a + 2 * m + 4) 1
  rw [show 1 + (2 * m + 5) = 2 * m + 6 from by ring] at h
  exact h

-- Odd transition for m=0
theorem odd_trans_0 : ∀ a, ⟨a+1, 0, 0, 0, 1⟩ [fm]⊢⁺ ⟨a+2, 0, 0, 0, 4⟩ := by
  intro a
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 0, 1⟩ = some ⟨a, 1, 0, 1, 1⟩; simp [fm]
  step fm; step fm; step fm
  apply stepStar_trans (c_to_e 3 (a + 2) 1)
  rw [show 1 + 3 = 4 from by ring]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 3 ∧ 2 * a ≥ e + 1)
  · intro c ⟨a, e, hq, he3, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      have hk2 : k ≥ 2 := by omega
      have ha' : a ≥ k + 1 := by omega
      obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha'
      refine ⟨⟨a' + 2 * k + 2, 0, 0, 0, 2 * k + 3⟩,
              ⟨a' + 2 * k + 2, 2 * k + 3, rfl, by omega, by omega⟩, ?_⟩
      have h := even_trans (k - 1) a'
      have : a' + (k - 1) + 2 = a' + k + 1 := by omega
      have : 2 * (k - 1) + 2 = 2 * k := by omega
      have : a' + 2 * (k - 1) + 4 = a' + 2 * k + 2 := by omega
      have : 2 * (k - 1) + 5 = 2 * k + 3 := by omega
      simp only [*] at h
      rw [show k + 1 + a' = a' + k + 1 from by ring,
          show k + k = 2 * k from by ring]
      exact h
    · subst hk
      have hk1 : k ≥ 1 := by omega
      have ha' : a ≥ k + 1 := by omega
      obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha'
      refine ⟨⟨a' + 2 * k + 2, 0, 0, 0, 2 * k + 4⟩,
              ⟨a' + 2 * k + 2, 2 * k + 4, rfl, by omega, by omega⟩, ?_⟩
      have h := odd_trans (k - 1) a'
      have : a' + (k - 1) + 2 = a' + k + 1 := by omega
      have : 2 * (k - 1) + 3 = 2 * k + 1 := by omega
      have : a' + 2 * (k - 1) + 4 = a' + 2 * k + 2 := by omega
      have : 2 * (k - 1) + 6 = 2 * k + 4 := by omega
      simp only [*] at h
      rw [show k + 1 + a' = a' + k + 1 from by ring,
          show 2 * k + 1 = 2 * k + 1 from rfl]
      exact h
  · exact ⟨2, 3, rfl, by omega, by omega⟩

end Sz21_140_unofficial_105
