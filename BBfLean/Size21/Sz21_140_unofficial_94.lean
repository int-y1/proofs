import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #94: [5/6, 8/35, 77/2, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 3  0 -1 -1  0
-1  0  0  1  1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_94

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3 chain
theorem r3_chain : ∀ k, ∀ a d e, ⟨a+k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d+k, e+k⟩ := by
  intro k; induction' k with k h <;> intro a d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R4 chain
theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R3-R2 chain
theorem r3r2_chain : ∀ k, ∀ a c e, ⟨a+1, 0, c+k, 0, e⟩ [fm]⊢* ⟨a+1+2*k, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm
  rw [show a + 3 = (a + 2) + 1 from by ring]
  apply stepStar_trans (h (a + 2) c (e + 1)); ring_nf; finish

-- Round lemma
theorem round_lemma : ∀ B C E, ⟨0, B+4, C, 0, E+1⟩ [fm]⊢* ⟨0, B, C+3, 0, E⟩ := by
  intro B C E
  step fm
  rw [show B + 4 = (B + 3) + 1 from by ring]; step fm
  step fm
  rw [show B + 3 = (B + 2) + 1 from by ring]; step fm
  rw [show B + 2 = (B + 1) + 1 from by ring]; step fm
  step fm; finish

-- Iterate round lemma
theorem rounds : ∀ k, ∀ r C E, ⟨0, 4*k+r, C, 0, E+k⟩ [fm]⊢* ⟨0, r, C+3*k, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro r C E
  · simp; exists 0
  rw [show 4 * (k + 1) + r = (4 * k + r) + 4 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  apply stepStar_trans (round_lemma (4 * k + r) C (E + k))
  rw [show C + 3 * (k + 1) = (C + 3) + 3 * k from by ring]
  exact ih r (C + 3) E

-- Tail b=0
theorem tail_b0 (C E : ℕ) : ⟨0, 0, C+1, 0, E+1⟩ [fm]⊢⁺ ⟨2*C+4, 0, 0, 0, E+C⟩ := by
  step fm; step fm
  have h := r3r2_chain C 3 0 E
  simp only [Nat.zero_add] at h
  refine stepStar_trans ?_ (by ring_nf; finish)
  convert h using 2; all_goals ring_nf

-- Tail b=1
theorem tail_b1 (C E : ℕ) : ⟨0, 1, C, 0, E+1⟩ [fm]⊢⁺ ⟨2*C+3, 0, 0, 0, E+C⟩ := by
  step fm; step fm; step fm
  have h := r3r2_chain C 2 0 E
  simp only [Nat.zero_add] at h
  refine stepStar_trans ?_ (by ring_nf; finish)
  convert h using 2; all_goals ring_nf

-- Tail b=2
theorem tail_b2 (C E : ℕ) : ⟨0, 2, C, 0, E+1⟩ [fm]⊢⁺ ⟨2*C+4, 0, 0, 0, E+C+1⟩ := by
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm
  have h := r3r2_chain C 3 0 (E + 1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans ?_ (by ring_nf; finish)
  convert h using 2; all_goals ring_nf

-- Tail b=3
theorem tail_b3 (C E : ℕ) : ⟨0, 3, C, 0, E+1⟩ [fm]⊢⁺ ⟨2*C+5, 0, 0, 0, E+C+2⟩ := by
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  step fm; step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm
  have h := r3r2_chain (C + 1) 2 0 (E + 1)
  simp only [Nat.zero_add] at h
  refine stepStar_trans ?_ (by ring_nf; finish)
  convert h using 2; all_goals ring_nf

-- Main transition
theorem main_trans (a e : ℕ) : ∃ a' e', (⟨a+1, 0, 0, 0, e⟩ : Q) [fm]⊢⁺ ⟨a'+1, 0, 0, 0, e'⟩ := by
  -- Phase 1+2
  have phase12 : (⟨a+1, 0, 0, 0, e⟩ : Q) [fm]⊢* ⟨0, a+1, 0, 0, e+(a+1)⟩ := by
    have h1 := r3_chain (a+1) 0 0 e
    have h2 := r4_chain (a+1) 0 0 (e+(a+1))
    simp only [Nat.zero_add] at h1 h2
    exact stepStar_trans h1 h2
  -- Decompose a+1 = 4k+r
  obtain ⟨k, r, hak, hr⟩ : ∃ k r, a + 1 = 4 * k + r ∧ r < 4 :=
    ⟨(a+1)/4, (a+1)%4, by omega, Nat.mod_lt _ (by omega)⟩
  -- Rounds
  have phase3 := rounds k r 0 (e + 3 * k + r)
  simp only [Nat.zero_add] at phase3
  have phase123 : (⟨a+1, 0, 0, 0, e⟩ : Q) [fm]⊢* ⟨0, r, 3*k, 0, e+3*k+r⟩ := by
    rw [hak] at phase12 ⊢
    rw [show e + (4 * k + r) = e + 3 * k + r + k from by omega] at phase12
    exact stepStar_trans phase12 phase3
  -- Dispatch on r ∈ {0,1,2,3}
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · -- r = 0
    have hk1 : k ≥ 1 := by omega
    refine ⟨6 * k + 1, e + 6 * k - 2, ?_⟩
    apply stepStar_stepPlus_stepPlus phase123
    have h := tail_b0 (3 * k - 1) (e + 3 * k - 1)
    rw [show 3 * k - 1 + 1 = 3 * k from by omega,
        show e + 3 * k - 1 + 1 = e + 3 * k from by omega,
        show 2 * (3 * k - 1) + 4 = 6 * k + 1 + 1 from by omega,
        show e + 3 * k - 1 + (3 * k - 1) = e + 6 * k - 2 from by omega] at h
    exact h
  · -- r = 1
    refine ⟨6 * k + 2, e + 6 * k, ?_⟩
    apply stepStar_stepPlus_stepPlus phase123
    have h := tail_b1 (3 * k) (e + 3 * k)
    rw [show 2 * (3 * k) + 3 = 6 * k + 2 + 1 from by omega,
        show e + 3 * k + (3 * k) = e + 6 * k from by omega] at h
    exact h
  · -- r = 2
    refine ⟨6 * k + 3, e + 6 * k + 2, ?_⟩
    apply stepStar_stepPlus_stepPlus phase123
    have h := tail_b2 (3 * k) (e + 3 * k + 1)
    rw [show e + 3 * k + 1 + 1 = e + 3 * k + 2 from by omega,
        show 2 * (3 * k) + 4 = 6 * k + 3 + 1 from by omega,
        show e + 3 * k + 1 + (3 * k) + 1 = e + 6 * k + 2 from by omega] at h
    exact h
  · -- r = 3
    refine ⟨6 * k + 4, e + 6 * k + 4, ?_⟩
    apply stepStar_stepPlus_stepPlus phase123
    have h := tail_b3 (3 * k) (e + 3 * k + 2)
    rw [show e + 3 * k + 2 + 1 = e + 3 * k + 3 from by omega,
        show 2 * (3 * k) + 5 = 6 * k + 4 + 1 from by omega,
        show e + 3 * k + 2 + (3 * k) + 2 = e + 6 * k + 4 from by omega] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = (⟨a + 1, 0, 0, 0, e⟩ : Q))
  · intro c ⟨a, e, hc⟩
    subst hc
    obtain ⟨a', e', h⟩ := main_trans a e
    exact ⟨⟨a' + 1, 0, 0, 0, e'⟩, ⟨a', e', rfl⟩, h⟩
  · exact ⟨0, 0, rfl⟩
