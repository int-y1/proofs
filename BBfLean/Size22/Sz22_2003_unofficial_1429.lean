import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1429: [7/15, 22/3, 27/77, 5/11, 363/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
 0  3  0 -1 -1
 0  0  1  0 -1
-1  1  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1429

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ a c, (⟨a, 0, c, 0, k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c; step fm
    apply stepStar_trans (ih a (c + 1)); ring_nf; finish

theorem drain_chain : ∀ k, ∀ a d e,
    (⟨a, 0, 0, d + k, e + 1⟩ : Q) [fm]⊢* ⟨a + 3 * k, 0, 0, d, e + 2 * k + 1⟩ := by
  intro k; induction k with
  | zero => intro a d e; ring_nf; finish
  | succ k ih =>
    intro a d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + 1 = e + 1 from rfl]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 3) d (e + 2)); ring_nf; finish

theorem r3_r1x3 : ∀ a c d e,
    (⟨a, 0, c + 3, d + 1, e + 1⟩ : Q) [fm]⊢* ⟨a, 0, c, d + 3, e⟩ := by
  intro a c d e; step fm; step fm; step fm; step fm; finish

theorem big_round : ∀ a c d,
    (⟨a + 1, 0, c + 7, d + 1, 2⟩ : Q) [fm]⊢* ⟨a, 0, c, d + 6, 2⟩ := by
  intro a c d; execute fm 10

theorem big_round_chain : ∀ k, ∀ a c d,
    (⟨a + k, 0, c + 7 * k, d + 1, 2⟩ : Q) [fm]⊢* ⟨a, 0, c, d + 5 * k + 1, 2⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; finish
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 7 * (k + 1) = (c + 7 * k) + 7 from by ring]
    apply stepStar_trans (big_round (a + k) (c + 7 * k) d)
    rw [show d + 6 = (d + 5) + 1 from by ring]
    apply stepStar_trans (ih a c (d + 5)); ring_nf; finish

theorem tail_c0 : ∀ a d,
    (⟨a, 0, 0, d + 1, 2⟩ : Q) [fm]⊢* ⟨a + 3, 0, 0, d, 4⟩ := by
  intro a d; execute fm 4

theorem tail_c1 : ∀ a d,
    (⟨a, 0, 1, d + 1, 2⟩ : Q) [fm]⊢* ⟨a + 2, 0, 0, d + 1, 3⟩ := by
  intro a d; execute fm 4

theorem tail_c2 : ∀ a d,
    (⟨a, 0, 2, d + 1, 2⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, d + 2, 2⟩ := by
  intro a d; execute fm 4

theorem tail_c3 : ∀ a d,
    (⟨a, 0, 3, d + 1, 2⟩ : Q) [fm]⊢* ⟨a, 0, 0, d + 3, 1⟩ := by
  intro a d; execute fm 4

theorem tail_c4 : ∀ a d,
    (⟨a, 0, 4, d + 1, 2⟩ : Q) [fm]⊢* ⟨a + 2, 0, 0, d + 3, 2⟩ := by
  intro a d; execute fm 8

theorem tail_c5 : ∀ a d,
    (⟨a, 0, 5, d + 1, 2⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, d + 4, 1⟩ := by
  intro a d; execute fm 8

theorem tail_c6 : ∀ a d,
    (⟨a + 1, 0, 6, d + 1, 2⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, d + 5, 3⟩ := by
  intro a d; execute fm 10

theorem opening2 : ∀ a e,
    (⟨a + 1, 0, 0, 0, e + 1⟩ : Q) [fm]⊢⁺ ⟨a, 0, e, 1, 2⟩ := by
  intro a e
  apply stepStar_stepPlus_stepPlus (e_to_c (e + 1) (a + 1) 0)
  rw [show 0 + (e + 1) = e + 1 from by ring]
  step fm; step fm
  ring_nf; finish

-- Full transition lemmas. Each takes (X, 0, 0, 0, E) to a new (X', 0, 0, 0, E').
-- Parameterized by K (number of big rounds) and a (offset).

-- e mod 7 = 5: E = 7K+6.
theorem full_r5 (K a : ℕ) :
    (⟨a + K + 1, 0, 0, 0, 7 * K + 6⟩ : Q) [fm]⊢⁺ ⟨a + 15 * K + 13, 0, 0, 0, 10 * K + 9⟩ := by
  rw [show 7 * K + 6 = (7 * K + 5) + 1 from by ring,
      show a + K + 1 = (a + K) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening2 (a + K) (7 * K + 5))
  rw [show 7 * K + 5 = 5 + 7 * K from by ring,
      show a + K = a + K from rfl]
  apply stepStar_trans (big_round_chain K a 5 0)
  rw [show 0 + 5 * K + 1 = 5 * K + 1 from by ring]
  apply stepStar_trans (tail_c5 a (5 * K))
  rw [show 5 * K + 4 = 0 + (5 * K + 4) from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (drain_chain (5 * K + 4) (a + 1) 0 0)
  ring_nf; finish

-- e mod 7 = 6: E = 7K+7.
theorem full_r6 (K a : ℕ) :
    (⟨a + K + 2, 0, 0, 0, 7 * K + 7⟩ : Q) [fm]⊢⁺ ⟨a + 15 * K + 16, 0, 0, 0, 10 * K + 13⟩ := by
  rw [show 7 * K + 7 = (7 * K + 6) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening2 (a + K + 1) (7 * K + 6))
  rw [show 7 * K + 6 = 6 + 7 * K from by ring,
      show a + K + 1 = (a + 1) + K from by ring]
  apply stepStar_trans (big_round_chain K (a + 1) 6 0)
  rw [show 0 + 5 * K + 1 = 5 * K + 1 from by ring]
  apply stepStar_trans (tail_c6 a (5 * K))
  rw [show 5 * K + 5 = 0 + (5 * K + 5) from by ring,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (drain_chain (5 * K + 5) (a + 1) 0 2)
  ring_nf; finish

-- e mod 7 = 0: E = 7K+8.
theorem full_r0 (K a : ℕ) :
    (⟨a + K + 2, 0, 0, 0, 7 * K + 8⟩ : Q) [fm]⊢⁺ ⟨a + 15 * K + 18, 0, 0, 0, 10 * K + 14⟩ := by
  rw [show 7 * K + 8 = (7 * K + 7) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening2 (a + K + 1) (7 * K + 7))
  rw [show a + K + 1 = a + (K + 1) from by ring]
  have h := big_round_chain (K + 1) a 0 0
  rw [show 0 + 7 * (K + 1) = 7 * K + 7 from by ring,
      show 0 + 5 * (K + 1) + 1 = (5 * K + 5) + 1 from by ring] at h
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  apply stepStar_trans (tail_c0 a (5 * K + 5))
  have h2 := drain_chain (5 * K + 5) (a + 3) 0 3
  rw [show 0 + (5 * K + 5) = 5 * K + 5 from by ring] at h2
  apply stepStar_trans h2; ring_nf; finish

-- e mod 7 = 1: E = 7K+9.
theorem full_r1 (K a : ℕ) :
    (⟨a + K + 2, 0, 0, 0, 7 * K + 9⟩ : Q) [fm]⊢⁺ ⟨a + 15 * K + 20, 0, 0, 0, 10 * K + 15⟩ := by
  rw [show 7 * K + 9 = (7 * K + 8) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening2 (a + K + 1) (7 * K + 8))
  rw [show 7 * K + 8 = 1 + 7 * (K + 1) from by ring,
      show a + K + 1 = a + (K + 1) from by ring]
  have h := big_round_chain (K + 1) a 1 0
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  rw [show 5 * (K + 1) + 1 = (5 * K + 5) + 1 from by ring]
  apply stepStar_trans (tail_c1 a (5 * K + 5))
  rw [show 5 * K + 5 + 1 = 0 + (5 * K + 6) from by ring,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (drain_chain (5 * K + 6) (a + 2) 0 2)
  ring_nf; finish

-- e mod 7 = 2: E = 7K+10.
theorem full_r2 (K a : ℕ) :
    (⟨a + K + 2, 0, 0, 0, 7 * K + 10⟩ : Q) [fm]⊢⁺ ⟨a + 15 * K + 22, 0, 0, 0, 10 * K + 16⟩ := by
  rw [show 7 * K + 10 = (7 * K + 9) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening2 (a + K + 1) (7 * K + 9))
  rw [show 7 * K + 9 = 2 + 7 * (K + 1) from by ring,
      show a + K + 1 = a + (K + 1) from by ring]
  have h := big_round_chain (K + 1) a 2 0
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  rw [show 5 * (K + 1) + 1 = (5 * K + 5) + 1 from by ring]
  apply stepStar_trans (tail_c2 a (5 * K + 5))
  have h2 := drain_chain (5 * K + 7) (a + 1) 0 1
  rw [show 0 + (5 * K + 7) = 5 * K + 5 + 2 from by ring] at h2
  apply stepStar_trans h2; ring_nf; finish

-- e mod 7 = 3: E = 7K+11.
theorem full_r3 (K a : ℕ) :
    (⟨a + K + 2, 0, 0, 0, 7 * K + 11⟩ : Q) [fm]⊢⁺ ⟨a + 15 * K + 24, 0, 0, 0, 10 * K + 17⟩ := by
  rw [show 7 * K + 11 = (7 * K + 10) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening2 (a + K + 1) (7 * K + 10))
  rw [show 7 * K + 10 = 3 + 7 * (K + 1) from by ring,
      show a + K + 1 = a + (K + 1) from by ring]
  have h := big_round_chain (K + 1) a 3 0
  rw [show 0 + 5 * (K + 1) + 1 = (5 * K + 5) + 1 from by ring] at h
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  apply stepStar_trans (tail_c3 a (5 * K + 5))
  rw [show 5 * K + 5 + 3 = 0 + (5 * K + 8) from by ring,
      show (1 : ℕ) = 0 + 1 from rfl]
  apply stepStar_trans (drain_chain (5 * K + 8) a 0 0)
  ring_nf; finish

-- e mod 7 = 4: E = 7K+12.
theorem full_r4 (K a : ℕ) :
    (⟨a + K + 2, 0, 0, 0, 7 * K + 12⟩ : Q) [fm]⊢⁺ ⟨a + 15 * K + 26, 0, 0, 0, 10 * K + 18⟩ := by
  rw [show 7 * K + 12 = (7 * K + 11) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening2 (a + K + 1) (7 * K + 11))
  rw [show 7 * K + 11 = 4 + 7 * (K + 1) from by ring,
      show a + K + 1 = a + (K + 1) from by ring]
  have h := big_round_chain (K + 1) a 4 0
  rw [show 0 + 5 * (K + 1) + 1 = (5 * K + 5) + 1 from by ring] at h
  simp only [Nat.zero_add] at h
  apply stepStar_trans h
  apply stepStar_trans (tail_c4 a (5 * K + 5))
  have h2 := drain_chain (5 * K + 8) (a + 2) 0 1
  rw [show 0 + (5 * K + 8) = 5 * K + 5 + 3 from by ring] at h2
  apply stepStar_trans h2; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 6⟩) (by execute fm 19)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ X E, q = ⟨X, 0, 0, 0, E⟩ ∧ X ≥ E ∧ E ≥ 6)
  · intro q ⟨X, E, hq, hXE, hE6⟩; subst hq
    have h7 : E % 7 = 0 ∨ E % 7 = 1 ∨ E % 7 = 2 ∨ E % 7 = 3 ∨
              E % 7 = 4 ∨ E % 7 = 5 ∨ E % 7 = 6 := by omega
    obtain ⟨K, hEK⟩ : ∃ K, E = 7 * K + E % 7 := ⟨E / 7, by omega⟩
    rcases h7 with h | h | h | h | h | h | h <;> rw [h] at hEK <;> subst hEK
    · -- E = 7K, K >= 1
      have hK1 : K ≥ 1 := by omega
      have hp := full_r6 (K - 1) (X - K - 1)
      rw [show X - K - 1 + (K - 1) + 2 = X from by omega,
          show 7 * (K - 1) + 7 = 7 * K + 0 from by omega] at hp
      exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, hp⟩
    · -- E = 7K+1, K >= 1
      have hK1 : K ≥ 1 := by omega
      have hp := full_r0 (K - 1) (X - K - 1)
      rw [show X - K - 1 + (K - 1) + 2 = X from by omega,
          show 7 * (K - 1) + 8 = 7 * K + 1 from by omega] at hp
      exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, hp⟩
    · -- E = 7K+2, K >= 1
      have hK1 : K ≥ 1 := by omega
      have hp := full_r1 (K - 1) (X - K - 1)
      rw [show X - K - 1 + (K - 1) + 2 = X from by omega,
          show 7 * (K - 1) + 9 = 7 * K + 2 from by omega] at hp
      exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, hp⟩
    · -- E = 7K+3, K >= 1
      have hK1 : K ≥ 1 := by omega
      have hp := full_r2 (K - 1) (X - K - 1)
      rw [show X - K - 1 + (K - 1) + 2 = X from by omega,
          show 7 * (K - 1) + 10 = 7 * K + 3 from by omega] at hp
      exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, hp⟩
    · -- E = 7K+4, K >= 1
      have hK1 : K ≥ 1 := by omega
      have hp := full_r3 (K - 1) (X - K - 1)
      rw [show X - K - 1 + (K - 1) + 2 = X from by omega,
          show 7 * (K - 1) + 11 = 7 * K + 4 from by omega] at hp
      exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, hp⟩
    · -- E = 7K+5, K >= 1
      have hK1 : K ≥ 1 := by omega
      have hp := full_r4 (K - 1) (X - K - 1)
      rw [show X - K - 1 + (K - 1) + 2 = X from by omega,
          show 7 * (K - 1) + 12 = 7 * K + 5 from by omega] at hp
      exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, hp⟩
    · -- E = 7K+6
      have hp := full_r5 K (X - K - 1)
      rw [show X - K - 1 + K + 1 = X from by omega] at hp
      exact ⟨_, ⟨_, _, rfl, by omega, by omega⟩, hp⟩
  · exact ⟨7, 6, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1429
