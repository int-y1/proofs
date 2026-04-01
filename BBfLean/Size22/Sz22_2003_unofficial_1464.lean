import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1464: [7/15, 3/77, 50/7, 11/5, 315/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1  0  2 -1  0
 0  0 -1  0  1
-1  2  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1464

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c+1, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c d, ⟨a, (0 : ℕ), c, d + k, 0⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; simp; exists 0
  | succ k ih =>
    intro a c d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (c + 2) d)
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ a c e, ⟨a, (0 : ℕ), c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c (e + 1))
    ring_nf; finish

theorem r5r1r2r2_drain : ∀ k, ∀ a b e,
    ⟨a + k, b, (0 : ℕ), 0, e + 2 * k⟩ [fm]⊢* ⟨a, b + 3 * k, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; simp; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a (b + 3) e)
    ring_nf; finish

theorem r3r1r1_chain : ∀ j, ∀ a b d,
    ⟨a, b + 2 * j, (0 : ℕ), d + 1, 0⟩ [fm]⊢* ⟨a + j, b, 0, d + 1 + j, 0⟩ := by
  intro j; induction j with
  | zero => intro a b d; simp; exists 0
  | succ j ih =>
    intro a b d
    rw [show b + 2 * (j + 1) = (b + 2 * j) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) b (d + 1))
    ring_nf; finish

theorem b0_finish : ∀ a d,
    ⟨a, (0 : ℕ), 0, d, 0⟩ [fm]⊢* ⟨a + d, 0, 0, 0, 2 * d⟩ := by
  intro a d
  rw [show (0 : ℕ) = 0 + 0 from by ring, show d = 0 + d from by ring]
  apply stepStar_trans (r3_chain d a 0 0)
  rw [show 0 + 2 * d = 2 * d from by ring, show 2 * d = 0 + 2 * d from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (r4_chain (2 * d) (a + d) 0 0)
  ring_nf; finish

theorem b1_finish : ∀ a d,
    ⟨a, (1 : ℕ), 0, d + 1, 0⟩ [fm]⊢* ⟨a + d + 2, 0, 0, 0, 2 * d + 3⟩ := by
  intro a d
  step fm; step fm
  -- Now (a+1, 0, 1, d+1, 0). Use r3_chain with c=1.
  rw [show (1 : ℕ) = 1 from rfl, show d + 1 = 0 + (d + 1) from by ring]
  apply stepStar_trans (r3_chain (d + 1) (a + 1) 1 0)
  rw [show 1 + 2 * (d + 1) = 2 * d + 3 from by ring,
      show a + 1 + (d + 1) = a + d + 2 from by ring,
      show 2 * d + 3 = 0 + (2 * d + 3) from by ring]
  apply stepStar_trans (r4_chain (2 * d + 3) (a + d + 2) 0 0)
  ring_nf; finish

theorem odd_tail : ∀ a b,
    ⟨a + 1, b, (0 : ℕ), 0, 1⟩ [fm]⊢* ⟨a + 1, b, 0, 2, 0⟩ := by
  intro a b
  step fm; step fm; step fm; step fm; step fm; step fm
  finish

theorem build_b_even (j : ℕ) : ∀ a,
    ⟨a, 2 * j, (0 : ℕ), 2, 0⟩ [fm]⊢* ⟨a + 2 * j + 2, 0, 0, 0, 2 * (j + 2)⟩ := by
  intro a
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring, show 2 * j = 0 + 2 * j from by ring]
  apply stepStar_trans (r3r1r1_chain j a 0 (0 + 1))
  rw [show 0 + 1 + 1 + j = j + 2 from by ring]
  apply stepStar_trans (b0_finish (a + j) (j + 2))
  ring_nf; finish

theorem build_b_odd (j : ℕ) : ∀ a,
    ⟨a, 2 * j + 1, (0 : ℕ), 2, 0⟩ [fm]⊢* ⟨a + 2 * j + 3, 0, 0, 0, 2 * j + 5⟩ := by
  intro a
  rw [show 2 * j + 1 = 1 + 2 * j from by ring, show (2 : ℕ) = 0 + 1 + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain j a 1 (0 + 1))
  rw [show 0 + 1 + 1 + j = (j + 1) + 1 from by ring]
  apply stepStar_trans (b1_finish (a + j) (j + 1))
  ring_nf; finish

-- Even: (a+K+2, 0, 0, 0, 2K+2) ⊢* (a+3K+6, 0, 0, 0, 3K+8)
theorem main_even_star (K : ℕ) : ∀ a,
    ⟨a + K + 2, (0 : ℕ), 0, 0, 2 * K + 2⟩ [fm]⊢* ⟨a + 3 * K + 6, 0, 0, 0, 3 * K + 8⟩ := by
  intro a
  -- Drain K+1 rounds
  rw [show a + K + 2 = (a + 1) + (K + 1) from by ring,
      show 2 * K + 2 = 0 + 2 * (K + 1) from by ring]
  apply stepStar_trans (r5r1r2r2_drain (K + 1) (a + 1) 0 0)
  rw [show 0 + 3 * (K + 1) = 3 * K + 3 from by ring]
  -- Now (a+1, 3K+3, 0, 0, 0). R5+R1.
  step fm; step fm
  -- Now (a, 3K+4, 0, 2, 0).
  rcases Nat.even_or_odd (3 * K + 4) with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [show j + j = 2 * j from by ring] at hj
    rw [show 3 * K + 4 = 2 * j from hj,
        show a + 3 * K + 6 = a + 2 * j + 2 from by omega,
        show 3 * K + 8 = 2 * (j + 2) from by omega]
    exact build_b_even j a
  · rw [show 3 * K + 4 = 2 * j + 1 from hj,
        show a + 3 * K + 6 = a + 2 * j + 3 from by omega,
        show 3 * K + 8 = 2 * j + 5 from by omega]
    exact build_b_odd j a

theorem main_even (K : ℕ) : ∀ a,
    ⟨a + K + 2, (0 : ℕ), 0, 0, 2 * K + 2⟩ [fm]⊢⁺ ⟨a + 3 * K + 6, 0, 0, 0, 3 * K + 8⟩ := by
  intro a
  exact stepStar_stepPlus (main_even_star K a)
    (by intro h; have := congr_arg (fun q : Q => q.2.2.2.2) h; simp at this; omega)

-- Odd K=0: (a+1, 0, 0, 0, 1) ⊢* (a+3, 0, 0, 0, 4)
theorem main_odd_base_star : ∀ a,
    ⟨a + 1, (0 : ℕ), 0, 0, 1⟩ [fm]⊢* ⟨a + 3, 0, 0, 0, 4⟩ := by
  intro a
  apply stepStar_trans (odd_tail a 0)
  rw [show a + 3 = (a + 1) + 2 from by ring, show (4 : ℕ) = 2 * 2 from by ring]
  exact b0_finish (a + 1) 2

-- Odd K>=1: (a+K+2, 0, 0, 0, 2K+3) ⊢* (a+3K+6, 0, 0, 0, 3K+7)
theorem main_odd_succ_star (K : ℕ) : ∀ a,
    ⟨a + K + 2, (0 : ℕ), 0, 0, 2 * K + 3⟩ [fm]⊢* ⟨a + 3 * K + 6, 0, 0, 0, 3 * K + 7⟩ := by
  intro a
  rw [show a + K + 2 = (a + 1) + (K + 1) from by ring,
      show 2 * K + 3 = 1 + 2 * (K + 1) from by ring]
  apply stepStar_trans (r5r1r2r2_drain (K + 1) (a + 1) 0 1)
  rw [show 0 + 3 * (K + 1) = 3 * K + 3 from by ring]
  apply stepStar_trans (odd_tail a (3 * K + 3))
  -- Now (a+1, 3K+3, 0, 2, 0).
  rcases Nat.even_or_odd (3 * K + 3) with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [show j + j = 2 * j from by ring] at hj
    rw [show 3 * K + 3 = 2 * j from hj,
        show a + 3 * K + 6 = a + 1 + 2 * j + 2 from by omega,
        show 3 * K + 7 = 2 * (j + 2) from by omega]
    exact build_b_even j (a + 1)
  · rw [show 3 * K + 3 = 2 * j + 1 from hj,
        show a + 3 * K + 6 = a + 1 + 2 * j + 3 from by omega,
        show 3 * K + 7 = 2 * j + 5 from by omega]
    exact build_b_odd j (a + 1)

theorem main_odd (K : ℕ) : ∀ a,
    ⟨a + K + 1, (0 : ℕ), 0, 0, 2 * K + 1⟩ [fm]⊢⁺ ⟨a + 3 * K + 3, 0, 0, 0, 3 * K + 4⟩ := by
  intro a
  rcases K with _ | K
  · simp
    exact stepStar_stepPlus (main_odd_base_star a)
      (by intro h; have := congr_arg (fun q : Q => q.2.2.2.2) h; simp at this)
  · rw [show a + (K + 1) + 1 = a + K + 2 from by ring,
        show 2 * (K + 1) + 1 = 2 * K + 3 from by ring,
        show a + 3 * (K + 1) + 3 = a + 3 * K + 6 from by ring,
        show 3 * (K + 1) + 4 = 3 * K + 7 from by ring]
    exact stepStar_stepPlus (main_odd_succ_star K a)
      (by intro h; have := congr_arg (fun q : Q => q.2.2.2.2) h; simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, (0 : ℕ), 0, 0, e⟩ ∧ a ≥ 1 ∧ e ≥ 1 ∧ 2 * a ≥ e + 1)
  · intro c ⟨A, E, hc, hA, hE, hinv⟩
    subst hc
    rcases Nat.even_or_odd E with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK
      rcases K with _ | K
      · omega
      · subst hK
        have ha : A = (A - K - 2) + K + 2 := by omega
        rw [ha, show 2 * (K + 1) = 2 * K + 2 from by ring]
        refine ⟨⟨(A - K - 2) + 3 * K + 6, 0, 0, 0, 3 * K + 8⟩,
               ⟨(A - K - 2) + 3 * K + 6, 3 * K + 8, rfl, by omega, by omega, by omega⟩,
               main_even K (A - K - 2)⟩
    · subst hK
      have ha : A = (A - K - 1) + K + 1 := by omega
      rw [ha]
      refine ⟨⟨(A - K - 1) + 3 * K + 3, 0, 0, 0, 3 * K + 4⟩,
             ⟨(A - K - 1) + 3 * K + 3, 3 * K + 4, rfl, by omega, by omega, by omega⟩,
             main_odd K (A - K - 1)⟩
  · exact ⟨3, 5, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1464
