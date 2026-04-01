import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1432: [7/15, 22/3, 9/77, 25/11, 847/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  1
 0  2  0 -1 -1
 0  0  2  0 -1
-1  0  0  1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1432

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | _ => none

-- R4 chain: convert e to c.
theorem e_to_c : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing c e
  · simp; exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c + 2) (e := e))
    ring_nf; finish

-- One drain cycle: 7 steps.
theorem drain_one : ⟨a + 1, 0, c + 4, d, 0⟩ [fm]⊢⁺ ⟨a, 0, c, d + 3, 0⟩ := by
  execute fm 7

-- Drain loop: k cycles.
theorem drain_loop : ∀ k, ⟨a + k, 0, 4 * k + c, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih generalizing a c d
  · simp; exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show 4 * (k + 1) + c = 4 * k + (c + 4) from by ring]
    apply stepStar_trans (ih (a := a + 1) (c := c + 4) (d := d))
    apply stepStar_trans (stepPlus_stepStar (drain_one (a := a) (c := c) (d := d + 3 * k)))
    ring_nf; finish

-- Drain at least one cycle: ⊢⁺
theorem drain_plus : ∀ k, ⟨a + k + 1, 0, 4 * (k + 1) + c, d, 0⟩ [fm]⊢⁺ ⟨a, 0, c, d + 3 * (k + 1), 0⟩ := by
  intro k
  rw [show a + k + 1 = (a + 1) + k from by ring,
      show 4 * (k + 1) + c = 4 * k + (c + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (drain_loop k (a := a + 1) (c := c + 4) (d := d))
  apply stepPlus_stepStar_stepPlus (drain_one (a := a) (c := c) (d := d + 3 * k))
  ring_nf; finish

-- Tail for c=2: 7 steps.
theorem tail_c2 : ⟨a + 1, 0, 2, d, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, d + 1, 2⟩ := by
  execute fm 7

-- One ascending cycle: 3 steps.
theorem ascending_one : ⟨a, 0, 0, d + 1, e + 1⟩ [fm]⊢* ⟨a + 2, 0, 0, d, e + 2⟩ := by
  step fm; step fm; step fm; finish

-- Ascending loop: k cycles. (a, 0, 0, d+k, e+1) ⊢* (a+2k, 0, 0, d, e+k+1)
theorem ascending : ∀ k, ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e + k + 1⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · simp; exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (a := a) (d := d + 1) (e := e))
    rw [show e + k + 1 = (e + k) + 1 from by ring]
    apply stepStar_trans (ascending_one (a := a + 2 * k) (d := d) (e := e + k))
    ring_nf; finish

-- Even case: full transition for e = 2*(m+1).
-- (a+m+2, 0, 0, 0, 2*(m+1)) ⊢⁺ (a+6*m+8, 0, 0, 0, 3*m+6)
theorem trans_even (m : ℕ) :
    ⟨a + m + 2, 0, 0, 0, 2 * (m + 1)⟩ [fm]⊢⁺ ⟨a + 6 * m + 8, 0, 0, 0, 3 * m + 6⟩ := by
  -- e_to_c ⊢* then drain_plus ⊢⁺ then r5 ⊢* then ascending ⊢*
  apply stepStar_stepPlus_stepPlus
  · -- e_to_c
    rw [show 2 * (m + 1) = 0 + 2 * (m + 1) from by ring]
    apply stepStar_trans (e_to_c (2 * (m + 1)) (a := a + m + 2) (c := 0) (e := 0))
    rw [show 0 + 2 * (2 * (m + 1)) = 4 * (m + 1) + 0 from by ring]; finish
  -- drain_plus(m+1 cycles)
  rw [show a + m + 2 = (a + 1) + m + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (drain_plus m (a := a + 1) (c := 0) (d := 0))
  rw [show 0 + 3 * (m + 1) = 3 * m + 3 from by ring]
  -- Now at (a+1, 0, 0, 3*m+3, 0). R5 fires.
  step fm
  -- Now at (a, 0, 0, 3*m+3+1, 2). Ascending.
  rw [show 3 * m + 3 + 1 = 0 + (3 * m + 4) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (ascending (3 * m + 4) (a := a) (d := 0) (e := 1))
  ring_nf; finish

-- Odd case: full transition for e = 2*m+1.
-- (a+m+1, 0, 0, 0, 2*m+1) ⊢⁺ (a+6*m+4, 0, 0, 0, 3*m+3)
theorem trans_odd (m : ℕ) :
    ⟨a + m + 1, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨a + 6 * m + 4, 0, 0, 0, 3 * m + 3⟩ := by
  rcases m with _ | m
  · -- m=0: (a+1, 0, 0, 0, 1) ⊢⁺ (a+4, 0, 0, 0, 3)
    -- e_to_c ⊢* then tail_c2 ⊢⁺ then ascending ⊢*
    apply stepStar_stepPlus_stepPlus
    · -- e_to_c: e=1
      rw [show (1 : ℕ) = 0 + 1 from by ring]
      apply stepStar_trans (e_to_c 1 (a := a + 1) (c := 0) (e := 0))
      simp; finish
    -- tail_c2: (a+1, 0, 2, 0, 0) ⊢⁺ (a+2, 0, 0, 1, 2)
    apply stepPlus_stepStar_stepPlus (tail_c2 (a := a) (d := 0))
    -- ascending 1 cycle
    rw [show 0 + 1 = 0 + 1 from rfl,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (ascending 1 (a := a + 2) (d := 0) (e := 1))
    ring_nf; finish
  -- m >= 1: e = 2*(m+1)+1 = 2*m+3
  -- e_to_c ⊢* then drain_plus ⊢⁺ then tail_c2 ⊢* then ascending ⊢*
  apply stepStar_stepPlus_stepPlus
  · -- e_to_c
    rw [show 2 * (m + 1) + 1 = 0 + (2 * m + 3) from by ring]
    apply stepStar_trans (e_to_c (2 * m + 3) (a := a + (m + 1) + 1) (c := 0) (e := 0))
    rw [show 0 + 2 * (2 * m + 3) = 4 * (m + 1) + (2 + 0) from by ring]; finish
  -- drain_plus(m+1 cycles)
  rw [show a + (m + 1) + 1 = (a + 1) + m + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (drain_plus m (a := a + 1) (c := 2 + 0) (d := 0))
  rw [show 0 + 3 * (m + 1) = 3 * m + 3 from by ring,
      show 2 + 0 = 2 from by ring]
  -- Now at (a+1, 0, 2, 3*m+3, 0). tail_c2 fires.
  apply stepStar_trans (stepPlus_stepStar (tail_c2 (a := a) (d := 3 * m + 3)))
  -- Now at (a+2, 0, 0, 3*m+4, 2). Ascending.
  rw [show 3 * m + 3 + 1 = 0 + (3 * m + 4) from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (ascending (3 * m + 4) (a := a + 2) (d := 0) (e := 1))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨10, 0, 0, 0, 6⟩) (by execute fm 33)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 2 ∧ a ≥ e / 2 + 1)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- e even: e = m + m = 2*m
      rw [show m + m = 2 * m from by ring] at hm; subst hm
      have hm1 : m ≥ 1 := by omega
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m' + 2 :=
        ⟨a - m' - 2, by omega⟩
      refine ⟨⟨a' + 6 * m' + 8, 0, 0, 0, 3 * m' + 6⟩,
        ⟨a' + 6 * m' + 8, 3 * m' + 6, rfl, by omega, by omega⟩,
        trans_even m'⟩
    · -- e odd: e = 2*m + 1
      subst hm
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m + 1 := ⟨a - m - 1, by omega⟩
      refine ⟨⟨a' + 6 * m + 4, 0, 0, 0, 3 * m + 3⟩,
        ⟨a' + 6 * m + 4, 3 * m + 3, rfl, by omega, by omega⟩, trans_odd m⟩
  · exact ⟨10, 6, rfl, by omega, by omega⟩
