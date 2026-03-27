import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #617: [35/6, 121/2, 8/55, 3/7, 15/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 3  0 -1  0 -1
 0  1  0 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_617

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- Drain phase: R3 + 3xR2, consuming c and growing e
theorem drain : ∀ k, ∀ c e, ⟨0, 0, c+k, D, e+k⟩ [fm]⊢* ⟨0, 0, c, D, e+6*k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  rw [show e + k + 2 + 2 + 2 = (e + 6) + k from by ring]
  apply stepStar_trans (h c (e + 6))
  ring_nf; finish

-- Interleaving for b = 3*k
theorem interleave_3k : ∀ k, ∀ c D E, ⟨3, 3*k, c, D, E+k⟩ [fm]⊢* ⟨0, 0, c+2*k, D+3*k, E+6⟩ := by
  intro k; induction' k with k ih <;> intro c D E
  · step fm; step fm; step fm; finish
  rw [show 3 * (k + 1) = (3 * k) + 3 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih (c + 2) (D + 3) E)
  ring_nf; finish

-- Interleaving for b = 3*k+1
theorem interleave_3k1 : ∀ k, ∀ c D E, ⟨3, 3*k+1, c, D, E+k⟩ [fm]⊢* ⟨0, 0, c+2*k+1, D+3*k+1, E+4⟩ := by
  intro k; induction' k with k ih <;> intro c D E
  · step fm; step fm; step fm; finish
  rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 3 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih (c + 2) (D + 3) E)
  ring_nf; finish

-- Interleaving for b = 3*k+2
theorem interleave_3k2 : ∀ k, ∀ c D E, ⟨3, 3*k+2, c, D, E+k⟩ [fm]⊢* ⟨0, 0, c+2*k+2, D+3*k+2, E+2⟩ := by
  intro k; induction' k with k ih <;> intro c D E
  · step fm; step fm; step fm; finish
  rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 3 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih (c + 2) (D + 3) E)
  ring_nf; finish

-- Transition for d ≡ 0 (mod 3)
theorem trans_mod0 : ⟨0, 0, 0, 3*q, 3*q+2+n⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*q+1, 12*q+9+n⟩ := by
  have h1 := d_to_b (d := 0) (e := 3*q+2+n) (3*q) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show 3*q+2+n = (3*q+n) + 1 + 1 from by ring]
  step fm; step fm
  rw [show 3*q + n = (2*q+n) + q from by ring]
  apply stepStar_trans (interleave_3k1 q 0 0 (2*q+n))
  rw [show (0 : ℕ) + 2*q + 1 = 0 + (2*q+1) from by ring,
      show (0 : ℕ) + 3*q + 1 = 3*q+1 from by ring,
      show (2*q+n) + 4 = (n+3) + (2*q+1) from by ring]
  apply stepStar_trans (drain (D := 3*q+1) (2*q+1) 0 (n+3))
  ring_nf; finish

-- Transition for d ≡ 1 (mod 3)
theorem trans_mod1 : ⟨0, 0, 0, 3*q+1, 3*q+3+n⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*q+2, 12*q+13+n⟩ := by
  have h1 := d_to_b (d := 0) (e := 3*q+3+n) (3*q+1) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show 3*q+3+n = (3*q+1+n) + 1 + 1 from by ring]
  step fm; step fm
  rw [show 3*q+1+1 = 3*q+2 from by ring,
      show 3*q+1+n = (2*q+1+n) + q from by ring]
  apply stepStar_trans (interleave_3k2 q 0 0 (2*q+1+n))
  rw [show (0 : ℕ) + 2*q + 2 = 0 + (2*q+2) from by ring,
      show (0 : ℕ) + 3*q + 2 = 3*q+2 from by ring,
      show (2*q+1+n) + 2 = (n+1) + (2*q+2) from by ring]
  apply stepStar_trans (drain (D := 3*q+2) (2*q+2) 0 (n+1))
  ring_nf; finish

-- Transition for d ≡ 2 (mod 3)
theorem trans_mod2 : ⟨0, 0, 0, 3*q+2, 3*q+4+n⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*q+3, 12*q+17+n⟩ := by
  have h1 := d_to_b (d := 0) (e := 3*q+4+n) (3*q+2) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  rw [show 3*q+4+n = (3*q+2+n) + 1 + 1 from by ring]
  step fm; step fm
  rw [show 3*q+2+1 = 3*(q+1) from by ring,
      show 3*q+2+n = (2*q+1+n) + (q+1) from by ring]
  apply stepStar_trans (interleave_3k (q+1) 0 0 (2*q+1+n))
  rw [show (0 : ℕ) + 2*(q+1) = 0 + (2*q+2) from by ring,
      show (0 : ℕ) + 3*(q+1) = 3*q+3 from by ring,
      show (2*q+1+n) + 6 = (n+5) + (2*q+2) from by ring]
  apply stepStar_trans (drain (D := 3*q+3) (2*q+2) 0 (n+5))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d E, q = ⟨0, 0, 0, d, E⟩ ∧ E ≥ d + 2)
  · intro c ⟨d, E, hq, hE⟩; subst hq
    have hd3 := Nat.div_add_mod d 3
    have hmod : d % 3 < 3 := Nat.mod_lt _ (by omega)
    rcases h : d % 3 with _ | _ | _ | r
    · -- d ≡ 0 mod 3
      obtain ⟨q, rfl⟩ : ∃ q, d = 3 * q := ⟨d / 3, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ n, E = 3*q + 2 + n := ⟨E - (3*q + 2), by omega⟩
      exact ⟨_, ⟨3*q+1, 12*q+9+n, rfl, by omega⟩, trans_mod0⟩
    · -- d ≡ 1 mod 3
      obtain ⟨q, rfl⟩ : ∃ q, d = 3 * q + 1 := ⟨d / 3, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ n, E = 3*q + 3 + n := ⟨E - (3*q + 3), by omega⟩
      exact ⟨_, ⟨3*q+2, 12*q+13+n, rfl, by omega⟩, trans_mod1⟩
    · -- d ≡ 2 mod 3
      obtain ⟨q, rfl⟩ : ∃ q, d = 3 * q + 2 := ⟨d / 3, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ n, E = 3*q + 4 + n := ⟨E - (3*q + 4), by omega⟩
      exact ⟨_, ⟨3*q+3, 12*q+17+n, rfl, by omega⟩, trans_mod2⟩
    · omega
  · exact ⟨0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_617
