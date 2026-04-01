import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #1431: [7/15, 22/3, 81/77, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
 0  4  0 -1 -1
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1431

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+4, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ a c e, (⟨a, 0, c, 0, e + k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- Variant that avoids the Nat.add 0 issue.
theorem e_to_c' : ∀ k, ∀ a c, (⟨a, 0, c, 0, k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k a c
  have := e_to_c k a c 0
  simp at this; exact this

theorem r3r2_chain : ∀ k, ∀ a e, (⟨a, 0, 0, k, e + 1⟩ : Q) [fm]⊢* ⟨a + 4 * k, 0, 0, 0, e + 3 * k + 1⟩ := by
  intro k; induction k with
  | zero => intro a e; ring_nf; finish
  | succ k ih =>
    intro a e
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 4) (e + 3))
    ring_nf; finish

theorem middle_round : ∀ a c d, (⟨a + 1, 0, c + 6, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, c + 1, d + 4, 0⟩ := by
  intro a c d
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem rounds : ∀ k, ∀ a c d, (⟨a + k, 0, 5 * k + (c + 1), d, 0⟩ : Q) [fm]⊢* ⟨a, 0, c + 1, d + 4 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; finish
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show 5 * (k + 1) + (c + 1) = (5 * k + c) + 6 from by ring]
    apply stepStar_trans (middle_round (a + k) (5 * k + c) d)
    rw [show 5 * k + c + 1 = 5 * k + (c + 1) from by ring]
    apply stepStar_trans (ih a c (d + 4))
    ring_nf; finish

theorem exit_c1 : ∀ a d, (⟨a + 1, 0, 1, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, 0, d + 1, 1⟩ := by
  intro a d; step fm; step fm; finish

theorem exit_c2 : ∀ a d, (⟨a + 1, 0, 2, d, 0⟩ : Q) [fm]⊢* ⟨a + 3, 0, 0, d + 1, 3⟩ := by
  intro a d; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem exit_c3 : ∀ a d, (⟨a + 1, 0, 3, d, 0⟩ : Q) [fm]⊢* ⟨a + 2, 0, 0, d + 2, 2⟩ := by
  intro a d; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem exit_c4 : ∀ a d, (⟨a + 1, 0, 4, d, 0⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, d + 3, 1⟩ := by
  intro a d; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem exit_c5 : ∀ a d, (⟨a + 1, 0, 5, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, 0, d + 4, 0⟩ := by
  intro a d; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

theorem r5r2_entry : ∀ a d, (⟨a + 1, 0, 0, d + 1, 0⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, d + 1, 2⟩ := by
  intro a d; step fm; step fm; ring_nf; finish

-- e+2 = 5m+1, m >= 1: (a+m+1, 0, 0, 0, 5m+1) ⊢⁺ (a+16m+4, 0, 0, 0, 12m+4)
theorem trans_r1 (a m : ℕ) :
    (⟨a + m + 1, 0, 0, 0, 5 * m + 1⟩ : Q) [fm]⊢⁺ ⟨a + 16 * m + 4, 0, 0, 0, 12 * m + 4⟩ := by
  rw [show (5 * m + 1 : ℕ) = (5 * m) + 1 from by ring]
  step fm
  apply stepStar_trans (e_to_c' (5 * m) (a + m + 1) 1)
  rw [show 1 + 5 * m = 5 * m + 1 from by ring,
      show a + m + 1 = (a + 1) + m from by ring,
      show 5 * m + 1 = 5 * m + (0 + 1) from by ring]
  apply stepStar_trans (rounds m (a + 1) 0 0)
  rw [show 0 + 4 * m = 4 * m from by ring]
  apply stepStar_trans (exit_c1 a (4 * m))
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (4 * m + 1) a 0)
  rw [show a + 4 * (4 * m + 1) = a + 16 * m + 4 from by ring,
      show 0 + 3 * (4 * m + 1) + 1 = 12 * m + 4 from by ring]
  finish

-- e+2 = 5m+2: (a+m+1, 0, 0, 0, 5m+2) ⊢⁺ (a+16m+7, 0, 0, 0, 12m+6)
theorem trans_r2 (a m : ℕ) :
    (⟨a + m + 1, 0, 0, 0, 5 * m + 2⟩ : Q) [fm]⊢⁺ ⟨a + 16 * m + 7, 0, 0, 0, 12 * m + 6⟩ := by
  rw [show (5 * m + 2 : ℕ) = (5 * m + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (e_to_c' (5 * m + 1) (a + m + 1) 1)
  rw [show 1 + (5 * m + 1) = 5 * m + 2 from by ring,
      show a + m + 1 = (a + 1) + m from by ring,
      show 5 * m + 2 = 5 * m + (1 + 1) from by ring]
  apply stepStar_trans (rounds m (a + 1) 1 0)
  rw [show 0 + 4 * m = 4 * m from by ring]
  apply stepStar_trans (exit_c2 a (4 * m))
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (4 * m + 1) (a + 3) 2)
  rw [show a + 3 + 4 * (4 * m + 1) = a + 16 * m + 7 from by ring,
      show 2 + 3 * (4 * m + 1) + 1 = 12 * m + 6 from by ring]
  finish

-- e+2 = 5m+3: (a+m+1, 0, 0, 0, 5m+3) ⊢⁺ (a+16m+10, 0, 0, 0, 12m+8)
theorem trans_r3 (a m : ℕ) :
    (⟨a + m + 1, 0, 0, 0, 5 * m + 3⟩ : Q) [fm]⊢⁺ ⟨a + 16 * m + 10, 0, 0, 0, 12 * m + 8⟩ := by
  rw [show (5 * m + 3 : ℕ) = (5 * m + 2) + 1 from by ring]
  step fm
  apply stepStar_trans (e_to_c' (5 * m + 2) (a + m + 1) 1)
  rw [show 1 + (5 * m + 2) = 5 * m + 3 from by ring,
      show a + m + 1 = (a + 1) + m from by ring,
      show 5 * m + 3 = 5 * m + (2 + 1) from by ring]
  apply stepStar_trans (rounds m (a + 1) 2 0)
  rw [show 0 + 4 * m = 4 * m from by ring]
  apply stepStar_trans (exit_c3 a (4 * m))
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (4 * m + 2) (a + 2) 1)
  rw [show a + 2 + 4 * (4 * m + 2) = a + 16 * m + 10 from by ring,
      show 1 + 3 * (4 * m + 2) + 1 = 12 * m + 8 from by ring]
  finish

-- e+2 = 5m+4: (a+m+1, 0, 0, 0, 5m+4) ⊢⁺ (a+16m+13, 0, 0, 0, 12m+10)
theorem trans_r4 (a m : ℕ) :
    (⟨a + m + 1, 0, 0, 0, 5 * m + 4⟩ : Q) [fm]⊢⁺ ⟨a + 16 * m + 13, 0, 0, 0, 12 * m + 10⟩ := by
  rw [show (5 * m + 4 : ℕ) = (5 * m + 3) + 1 from by ring]
  step fm
  apply stepStar_trans (e_to_c' (5 * m + 3) (a + m + 1) 1)
  rw [show 1 + (5 * m + 3) = 5 * m + 4 from by ring,
      show a + m + 1 = (a + 1) + m from by ring,
      show 5 * m + 4 = 5 * m + (3 + 1) from by ring]
  apply stepStar_trans (rounds m (a + 1) 3 0)
  rw [show 0 + 4 * m = 4 * m from by ring,
      show 3 + 1 = 4 from by ring]
  apply stepStar_trans (exit_c4 a (4 * m))
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (4 * m + 3) (a + 1) 0)
  rw [show a + 1 + 4 * (4 * m + 3) = a + 16 * m + 13 from by ring,
      show 0 + 3 * (4 * m + 3) + 1 = 12 * m + 10 from by ring]
  finish

-- e+2 = 5(m+1): (a+m+2, 0, 0, 0, 5m+5) ⊢⁺ (a+16m+17, 0, 0, 0, 12m+14)
theorem trans_r0 (a m : ℕ) :
    (⟨a + m + 2, 0, 0, 0, 5 * m + 5⟩ : Q) [fm]⊢⁺ ⟨a + 16 * m + 17, 0, 0, 0, 12 * m + 14⟩ := by
  rw [show (5 * m + 5 : ℕ) = (5 * m + 4) + 1 from by ring]
  step fm
  apply stepStar_trans (e_to_c' (5 * m + 4) (a + m + 2) 1)
  rw [show 1 + (5 * m + 4) = 5 * m + 5 from by ring,
      show a + m + 2 = (a + 2) + m from by ring,
      show 5 * m + 5 = 5 * m + (4 + 1) from by ring]
  apply stepStar_trans (rounds m (a + 2) 4 0)
  rw [show 0 + 4 * m = 4 * m from by ring,
      show 4 + 1 = 5 from by ring]
  apply stepStar_trans (exit_c5 (a + 1) (4 * m))
  rw [show 4 * m + 4 = (4 * m + 3) + 1 from by ring]
  apply stepStar_trans (r5r2_entry a (4 * m + 3))
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (4 * m + 4) (a + 1) 1)
  rw [show a + 1 + 4 * (4 * m + 4) = a + 16 * m + 17 from by ring,
      show 1 + 3 * (4 * m + 4) + 1 = 12 * m + 14 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨7, 0, 0, 0, 6⟩) (by execute fm 16)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e + 2⟩ ∧ a ≥ e)
  · intro q ⟨a, e, hq, hae⟩; subst hq
    have h5 : (e + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
    obtain ⟨m, hm⟩ : ∃ m, e + 2 = 5 * m + (e + 2) % 5 := ⟨(e + 2) / 5, by omega⟩
    interval_cases ((e + 2) % 5)
    · -- (e+2) % 5 = 0: e+2 = 5m, m >= 1
      have hm1 : m ≥ 1 := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m' + 1 := ⟨a - m' - 1, by omega⟩
      refine ⟨⟨a' + 16 * m' + 17, 0, 0, 0, 12 * m' + 14⟩,
        ⟨a' + 16 * m' + 16, 12 * m' + 12, ?_, ?_⟩, ?_⟩
      · ring_nf
      · omega
      · have : e = 5 * m' + 3 := by omega
        rw [show a' + m' + 1 + 1 = a' + m' + 2 from by ring,
            show e + 2 = 5 * m' + 5 from by omega]
        exact trans_r0 a' m'
    · -- (e+2) % 5 = 1: e+2 = 5m+1, m >= 1
      have hm1 : m ≥ 1 := by omega
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m := ⟨a - m, by omega⟩
      refine ⟨⟨a' + 16 * m + 4, 0, 0, 0, 12 * m + 4⟩,
        ⟨a' + 16 * m + 3, 12 * m + 2, ?_, ?_⟩, ?_⟩
      · ring_nf
      · omega
      · rw [show e + 2 = 5 * m + 1 from by omega]
        exact trans_r1 a' m
    · -- (e+2) % 5 = 2: e+2 = 5m+2
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m := ⟨a - m, by omega⟩
      refine ⟨⟨a' + 16 * m + 7, 0, 0, 0, 12 * m + 6⟩,
        ⟨a' + 16 * m + 6, 12 * m + 4, ?_, ?_⟩, ?_⟩
      · ring_nf
      · omega
      · rw [show e + 2 = 5 * m + 2 from by omega]
        exact trans_r2 a' m
    · -- (e+2) % 5 = 3: e+2 = 5m+3
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m := ⟨a - m, by omega⟩
      refine ⟨⟨a' + 16 * m + 10, 0, 0, 0, 12 * m + 8⟩,
        ⟨a' + 16 * m + 9, 12 * m + 6, ?_, ?_⟩, ?_⟩
      · ring_nf
      · omega
      · rw [show e + 2 = 5 * m + 3 from by omega]
        exact trans_r3 a' m
    · -- (e+2) % 5 = 4: e+2 = 5m+4
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m := ⟨a - m, by omega⟩
      refine ⟨⟨a' + 16 * m + 13, 0, 0, 0, 12 * m + 10⟩,
        ⟨a' + 16 * m + 12, 12 * m + 8, ?_, ?_⟩, ?_⟩
      · ring_nf
      · omega
      · rw [show e + 2 = 5 * m + 4 from by omega]
        exact trans_r4 a' m
  · exact ⟨6, 4, rfl, by omega⟩

end Sz22_2003_unofficial_1431
