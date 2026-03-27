import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #175: [1/45, 98/15, 3/7, 625/2, 7/5]

Vector representation:
```
 0 -2 -1  0
 1 -1 -1  2
 0  1  0 -1
-1  0  4  0
 0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_175

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+4, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b, c, d+1⟩
  | _ => none

private theorem R1_chain : ∀ k a b c d,
    ⟨a, b + 2 * k, c + k, d⟩ [fm]⊢* ⟨a, b, c, d⟩ := by
  intro k; induction k with
  | zero => intro a b c d; exists 0
  | succ k ih =>
    intro a b c d
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; exact ih a b c d

private theorem d_to_b : ∀ k a b d,
    ⟨a, b, (0 : ℕ), d + k⟩ [fm]⊢* ⟨a, b + k, (0 : ℕ), d⟩ := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) d)
    rw [show b + 1 + k = b + (k + 1) from by ring]; finish

private theorem R4_chain : ∀ k a c,
    ⟨a + k, (0 : ℕ), c, (0 : ℕ)⟩ [fm]⊢* ⟨a, (0 : ℕ), c + 4 * k, (0 : ℕ)⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 4))
    rw [show c + 4 + 4 * k = c + 4 * (k + 1) from by ring]; finish

private theorem phase1_chain : ∀ k a c d,
    ⟨a, (0 : ℕ), c + k, d + 1⟩ [fm]⊢* ⟨a + k, (0 : ℕ), c, d + k + 1⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (d + 1))
    rw [show a + 1 + k = a + (k + 1) from by ring,
        show d + 1 + k + 1 = d + (k + 1) + 1 from by ring]; finish

private theorem big_step_repeat : ∀ q a b,
    ⟨a + q, b + 8 * q, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢* ⟨a, b, (0 : ℕ), (0 : ℕ)⟩ := by
  intro q; induction q with
  | zero => intro a b; exists 0
  | succ q ih =>
    intro a b
    rw [show a + (q + 1) = (a + q) + 1 from by ring,
        show b + 8 * (q + 1) = (b + 8 * q) + 8 from by ring]
    -- big_step: R4 + R1x4
    step fm -- R4: ((a+q), (b+8q)+8, 4, 0)
    rw [show (b + 8 * q) + 8 = b + 8 * q + 2 * 4 from by ring,
        show (4 : ℕ) = 0 + 4 from by ring]
    apply stepStar_trans (R1_chain 4 (a + q) (b + 8 * q) 0 0)
    exact ih a b

private theorem rem0 : ∀ a,
    ⟨a + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 4 * a + 4, (0 : ℕ)⟩ := by
  intro a; step fm
  have h := R4_chain a 0 4
  rw [show 0 + a = a from by ring, show 4 + 4 * a = 4 * a + 4 from by ring] at h
  exact h

private theorem rem2 : ∀ a,
    ⟨a + 1, (2 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 4 * a + 3, (0 : ℕ)⟩ := by
  intro a; step fm
  rw [show (2 : ℕ) = 0 + 2 * 1 from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (R1_chain 1 a 0 3 0)
  have h := R4_chain a 0 3
  rw [show 0 + a = a from by ring, show 3 + 4 * a = 4 * a + 3 from by ring] at h
  exact h

private theorem rem4 : ∀ a,
    ⟨a + 1, (4 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 4 * a + 2, (0 : ℕ)⟩ := by
  intro a; step fm
  show (a, 0 + 2 * 2, 2 + 2, 0) [fm]⊢* (0, 0, 4 * a + 2, 0)
  apply stepStar_trans (R1_chain 2 a 0 2 0)
  have h := R4_chain a 0 2
  rw [show 0 + a = a from by ring, show 2 + 4 * a = 4 * a + 2 from by ring] at h
  exact h

private theorem rem6 : ∀ a,
    ⟨a + 1, (6 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 4 * a + 1, (0 : ℕ)⟩ := by
  intro a; step fm
  rw [show (6 : ℕ) = 0 + 2 * 3 from by ring,
      show (4 : ℕ) = 1 + 3 from by ring]
  apply stepStar_trans (R1_chain 3 a 0 1 0)
  have h := R4_chain a 0 1
  rw [show 0 + a = a from by ring, show 1 + 4 * a = 4 * a + 1 from by ring] at h
  exact h

private theorem rem7 : ∀ a,
    ⟨a + 1, (7 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 4 * a + 3, (0 : ℕ)⟩ := by
  intro a
  apply stepPlus_trans (c₂ := ⟨a + 1, 2, 0, 0⟩)
  · step fm
    rw [show (7 : ℕ) = 1 + 2 * 3 from by ring,
        show (4 : ℕ) = 1 + 3 from by ring]
    apply stepStar_trans (R1_chain 3 a 1 1 0)
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 0 + 2 from by ring]
    exact d_to_b 2 (a + 1) 0 0
  · exact rem2 a

private theorem rem3 : ∀ a,
    ⟨a + 1, (3 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 4 * a + 10, (0 : ℕ)⟩ := by
  intro a
  apply stepPlus_trans (c₂ := ⟨a + 3, 4, 0, 0⟩)
  · step fm
    rw [show (3 : ℕ) = 1 + 2 * 1 from by ring,
        show (4 : ℕ) = 3 + 1 from by ring]
    apply stepStar_trans (R1_chain 1 a 1 3 0)
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    step fm
    rw [show (2 : ℕ) = 0 + 2 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (phase1_chain 2 (a + 1) 0 1)
    rw [show a + 1 + 2 = a + 3 from by ring,
        show 1 + 2 + 1 = 0 + 4 from by ring]
    exact d_to_b 4 (a + 3) 0 0
  · rw [show a + 3 = (a + 2) + 1 from by ring]
    have h := rem4 (a + 2)
    rw [show 4 * (a + 2) + 2 = 4 * a + 10 from by ring] at h; exact h

private theorem rem5 : ∀ a,
    ⟨a + 1, (5 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 4 * a + 14, (0 : ℕ)⟩ := by
  intro a
  apply stepPlus_trans (c₂ := ⟨a + 2, 3, 0, 0⟩)
  · step fm
    rw [show (5 : ℕ) = 1 + 2 * 2 from by ring,
        show (4 : ℕ) = 2 + 2 from by ring]
    apply stepStar_trans (R1_chain 2 a 1 2 0)
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (phase1_chain 1 (a + 1) 0 1)
    rw [show a + 1 + 1 = a + 2 from by ring,
        show 1 + 1 + 1 = 0 + 3 from by ring]
    exact d_to_b 3 (a + 2) 0 0
  · rw [show a + 2 = (a + 1) + 1 from by ring]
    have h := rem3 (a + 1)
    rw [show 4 * (a + 1) + 10 = 4 * a + 14 from by ring] at h; exact h

private theorem rem1 : ∀ a,
    ⟨a + 1, (1 : ℕ), (0 : ℕ), (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), 4 * a + 26, (0 : ℕ)⟩ := by
  intro a
  apply stepPlus_trans (c₂ := ⟨a + 4, 5, 0, 0⟩)
  · step fm
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show (4 : ℕ) = 3 + 1 from by ring]
    step fm
    rw [show (3 : ℕ) = 0 + 3 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (phase1_chain 3 (a + 1) 0 1)
    rw [show a + 1 + 3 = a + 4 from by ring,
        show 1 + 3 + 1 = 0 + 5 from by ring]
    exact d_to_b 5 (a + 4) 0 0
  · rw [show a + 4 = (a + 3) + 1 from by ring]
    have h := rem5 (a + 3)
    rw [show 4 * (a + 3) + 14 = 4 * a + 26 from by ring] at h; exact h

private theorem phase12 : ∀ n,
    ⟨(0 : ℕ), (0 : ℕ), n + 2, (0 : ℕ)⟩ [fm]⊢⁺ ⟨n + 1, n + 2, (0 : ℕ), (0 : ℕ)⟩ := by
  intro n
  rw [show n + 2 = (n + 1) + 1 from by ring]
  apply step_stepStar_stepPlus (by rfl : fm ⟨0, 0, (n + 1) + 1, 0⟩ = some ⟨0, 0, n + 1, 1⟩)
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (phase1_chain (n + 1) 0 0 0)
  rw [show 0 + (n + 1) + 1 = 0 + (n + 2) from by ring,
      show 0 + (n + 1) = n + 1 from by ring]
  exact d_to_b (n + 2) (n + 1) 0 0

theorem main_trans : ∀ n : ℕ,
    ∃ m : ℕ, ⟨(0 : ℕ), (0 : ℕ), n + 2, (0 : ℕ)⟩ [fm]⊢⁺ ⟨(0 : ℕ), (0 : ℕ), m + 2, (0 : ℕ)⟩ := by
  intro n
  match n with
  | 0 => exact ⟨1, by execute fm 7⟩
  | 1 => exact ⟨12, by execute fm 25⟩
  | 2 => exact ⟨8, by execute fm 16⟩
  | 3 => exact ⟨24, by execute fm 43⟩
  | 4 => exact ⟨15, by execute fm 25⟩
  | 5 => exact ⟨21, by execute fm 34⟩
  | n + 6 =>
    have hp12 := phase12 (n + 6)
    -- After phase12: (n+7, n+8, 0, 0). We decompose n mod 8.
    -- For n = 8m+s (s=0..7), n+8 = 8(m+1)+s.
    -- big_step_repeat with q=m+1: (n+7-(m+1), s, 0, 0) = (7m+s+6, s, 0, 0).
    -- hq: n+7 = (7m+s+6) + (m+1). Since n=8m+s: 8m+s+7 = 7m+s+6+m+1 = 8m+s+7. ✓
    -- hr: n+8 = s + 8*(m+1). 8m+s+8 = s+8m+8. ✓
    -- Keep n as hypothesis instead of substituting
    obtain ⟨p, hp⟩ | ⟨p, hp⟩ := Nat.even_or_odd n
    · obtain ⟨j, hj⟩ | ⟨j, hj⟩ := Nat.even_or_odd p
      · obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Nat.even_or_odd j
        · -- n = 8m, s=0
          refine ⟨28 * m + 22, stepPlus_trans hp12 ?_⟩
          rw [show n + 6 + 1 = (7 * m + 6) + (m + 1) from by omega,
              show n + 6 + 2 = 0 + 8 * (m + 1) from by omega]
          apply stepStar_stepPlus_stepPlus (big_step_repeat (m + 1) (7 * m + 6) 0)
          rw [show 7 * m + 6 = (7 * m + 5) + 1 from by omega]
          have h := rem0 (7 * m + 5)
          rw [show 4 * (7 * m + 5) + 4 = 28 * m + 22 + 2 from by omega] at h; exact h
        · -- n = 8m+4, s=4
          refine ⟨28 * m + 36, stepPlus_trans hp12 ?_⟩
          rw [show n + 6 + 1 = (7 * m + 10) + (m + 1) from by omega,
              show n + 6 + 2 = 4 + 8 * (m + 1) from by omega]
          apply stepStar_stepPlus_stepPlus (big_step_repeat (m + 1) (7 * m + 10) 4)
          rw [show 7 * m + 10 = (7 * m + 9) + 1 from by omega]
          have h := rem4 (7 * m + 9)
          rw [show 4 * (7 * m + 9) + 2 = 28 * m + 36 + 2 from by omega] at h; exact h
      · obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Nat.even_or_odd j
        · -- n = 8m+2, s=2
          refine ⟨28 * m + 29, stepPlus_trans hp12 ?_⟩
          rw [show n + 6 + 1 = (7 * m + 8) + (m + 1) from by omega,
              show n + 6 + 2 = 2 + 8 * (m + 1) from by omega]
          apply stepStar_stepPlus_stepPlus (big_step_repeat (m + 1) (7 * m + 8) 2)
          rw [show 7 * m + 8 = (7 * m + 7) + 1 from by omega]
          have h := rem2 (7 * m + 7)
          rw [show 4 * (7 * m + 7) + 3 = 28 * m + 29 + 2 from by omega] at h; exact h
        · -- n = 8m+6, s=6
          refine ⟨28 * m + 43, stepPlus_trans hp12 ?_⟩
          rw [show n + 6 + 1 = (7 * m + 12) + (m + 1) from by omega,
              show n + 6 + 2 = 6 + 8 * (m + 1) from by omega]
          apply stepStar_stepPlus_stepPlus (big_step_repeat (m + 1) (7 * m + 12) 6)
          rw [show 7 * m + 12 = (7 * m + 11) + 1 from by omega]
          have h := rem6 (7 * m + 11)
          rw [show 4 * (7 * m + 11) + 1 = 28 * m + 43 + 2 from by omega] at h; exact h
    · obtain ⟨j, hj⟩ | ⟨j, hj⟩ := Nat.even_or_odd p
      · obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Nat.even_or_odd j
        · -- n = 8m+1, s=1
          refine ⟨28 * m + 48, stepPlus_trans hp12 ?_⟩
          rw [show n + 6 + 1 = (7 * m + 7) + (m + 1) from by omega,
              show n + 6 + 2 = 1 + 8 * (m + 1) from by omega]
          apply stepStar_stepPlus_stepPlus (big_step_repeat (m + 1) (7 * m + 7) 1)
          rw [show 7 * m + 7 = (7 * m + 6) + 1 from by omega]
          have h := rem1 (7 * m + 6)
          rw [show 4 * (7 * m + 6) + 26 = 28 * m + 48 + 2 from by omega] at h; exact h
        · -- n = 8m+5, s=5
          refine ⟨28 * m + 52, stepPlus_trans hp12 ?_⟩
          rw [show n + 6 + 1 = (7 * m + 11) + (m + 1) from by omega,
              show n + 6 + 2 = 5 + 8 * (m + 1) from by omega]
          apply stepStar_stepPlus_stepPlus (big_step_repeat (m + 1) (7 * m + 11) 5)
          rw [show 7 * m + 11 = (7 * m + 10) + 1 from by omega]
          have h := rem5 (7 * m + 10)
          rw [show 4 * (7 * m + 10) + 14 = 28 * m + 52 + 2 from by omega] at h; exact h
      · obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Nat.even_or_odd j
        · -- n = 8m+3, s=3
          refine ⟨28 * m + 40, stepPlus_trans hp12 ?_⟩
          rw [show n + 6 + 1 = (7 * m + 9) + (m + 1) from by omega,
              show n + 6 + 2 = 3 + 8 * (m + 1) from by omega]
          apply stepStar_stepPlus_stepPlus (big_step_repeat (m + 1) (7 * m + 9) 3)
          rw [show 7 * m + 9 = (7 * m + 8) + 1 from by omega]
          have h := rem3 (7 * m + 8)
          rw [show 4 * (7 * m + 8) + 10 = 28 * m + 40 + 2 from by omega] at h; exact h
        · -- n = 8m+7, s=7
          refine ⟨28 * m + 49, stepPlus_trans hp12 ?_⟩
          rw [show n + 6 + 1 = (7 * m + 13) + (m + 1) from by omega,
              show n + 6 + 2 = 7 + 8 * (m + 1) from by omega]
          apply stepStar_stepPlus_stepPlus (big_step_repeat (m + 1) (7 * m + 13) 7)
          rw [show 7 * m + 13 = (7 * m + 12) + 1 from by omega]
          have h := rem7 (7 * m + 12)
          rw [show 4 * (7 * m + 12) + 3 = 28 * m + 49 + 2 from by omega] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨(0 : ℕ), (0 : ℕ), 4, (0 : ℕ)⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨(0 : ℕ), (0 : ℕ), n + 2, (0 : ℕ)⟩) 2
  intro n
  obtain ⟨m, hm⟩ := main_trans n
  exact ⟨m, hm⟩

end Sz22_2003_unofficial_175
