import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #289: [14/15, 9/22, 25/2, 11/49, 22/5]

Vector representation:
```
 1 -1 -1  1  0
-1  2  0  0 -1
-1  0  2  0  0
 0  0  0 -2  1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_289

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 repeated
theorem r4_drain : ∀ k c e, ⟨(0 : ℕ), 0, c, 2 * k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro c e; simp; exists 0
  | succ k ih =>
    intro c e; rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; rw [show e + (k + 1) = (e + 1) + k from by ring]; exact ih c (e + 1)

-- R2 repeated
theorem r2_drain : ∀ k b d, ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction k with
  | zero => intro b d; simp; exists 0
  | succ k ih =>
    intro b d
    rw [show a + (k + 1) = (a + k) + 1 from by ring, show k + 1 = k + 1 from rfl]
    step fm; rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]; exact ih (b + 2) d

-- R3 repeated
theorem r3_drain : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 2 * k, d, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d; step fm
    rw [show c + 2 * (k + 1) = c + 2 + 2 * k from by ring]; exact ih (c + 2) d

-- Chew triple: R1, R1, R2
theorem chew_triple : ⟨a, 2, c + 2, d, e + 1⟩ [fm]⊢⁺ ⟨a + 1, 2, c, d + 2, e⟩ := by
  step fm; step fm; step fm; finish

-- Chew triples iterated
theorem chew_triples : ∀ k a c d e, ⟨a, 2, c + 2 * k, d, e + k⟩ [fm]⊢*
    ⟨a + k, 2, c, d + 2 * k, e⟩ := by
  intro k; induction k with
  | zero => intro a c d e; simp; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih a (c + 2) d (e + 1))
    rw [show a + (k + 1) = a + k + 1 from by ring,
        show d + 2 * (k + 1) = d + 2 * k + 2 from by ring]
    exact stepPlus_stepStar chew_triple

-- Build triple: R3, R1, R1
theorem build_triple : ⟨a + 1, b + 2, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 2, b, 0, d + 2, 0⟩ := by
  step fm; step fm; step fm; finish

-- Build triples iterated
theorem build_triples : ∀ k a b d, ⟨a + 1, b + 2 * k, 0, d, 0⟩ [fm]⊢*
    ⟨a + 1 + k, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a b d; simp; exists 0
  | succ k ih =>
    intro a b d
    rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring]
    apply stepStar_trans (ih a (b + 2) d)
    rw [show a + 1 + (k + 1) = a + 1 + k + 1 from by ring,
        show d + 2 * (k + 1) = d + 2 * k + 2 from by ring,
        show a + 1 + k = (a + k) + 1 from by ring]
    exact stepPlus_stepStar build_triple

-- Odd transition: C(2m+1) →⁺ C(2m+2)
theorem main_odd (m : ℕ) :
    ⟨0, 0, 2 * m + 3, 4 * m + 2, 0⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 2 * m + 4, 4 * m + 4, 0⟩ := by
  -- Start with one R4 step to get ⊢⁺
  rw [show 4 * m + 2 = 2 * (2 * m) + 2 from by ring,
      show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  -- First R4 to establish stepPlus
  step fm
  -- Remaining R4 steps
  apply stepStar_trans (r4_drain (2 * m) ((2 * m + 2) + 1) 1)
  rw [show 1 + 2 * m = 2 * m + 1 from by ring]
  -- R5: (0, 0, 2m+3, 0, 2m+1) → (1, 0, 2m+2, 0, 2m+2)
  rw [show (2 * m + 2 : ℕ) + 1 = (2 * m + 2) + 1 from by ring]
  step fm
  -- R2: (1, 0, 2m+2, 0, 2m+2) → (0, 2, 2m+2, 0, 2m+1)
  rw [show 2 * m + 1 + 1 = (2 * m + 1) + 1 from by ring]
  step fm
  -- Chew×(m+1): (0, 2, 2m+2, 0, 2m+1) → (m+1, 2, 0, 2m+2, m)
  rw [show 2 * m + 2 = 0 + 2 * (m + 1) from by ring,
      show 2 * m + 1 = m + (m + 1) from by ring]
  apply stepStar_trans (chew_triples (m + 1) 0 0 0 m)
  rw [show 0 + (m + 1) = m + 1 from by ring, show 0 + 2 * (m + 1) = 2 * (m + 1) from by ring]
  -- R2×m: (m+1, 2, 0, 2(m+1), m) → (1, 2+2m, 0, 2(m+1), 0)
  rw [show m + 1 = 1 + m from by ring, show 2 * (1 + m) = 2 * (m + 1) from by ring]
  apply stepStar_trans (r2_drain (a := 1) m 2 (2 * (m + 1)))
  rw [show 2 + 2 * m = 2 * m + 1 + 1 from by ring]
  -- R3: (1, 2m+2, 0, 2(m+1), 0) → (0, 2m+2, 2, 2(m+1), 0)
  step fm
  -- R1, R1: (0, 2m+2, 2, 2(m+1), 0) → (2, 2m, 0, 2(m+1)+2, 0)
  step fm; step fm
  -- Build×m
  have hb : ∀ d, ⟨(2 : ℕ), 2 * m, 0, d, 0⟩ [fm]⊢* ⟨m + 1 + 1, 0, 0, d + 2 * m, 0⟩ := by
    intro d
    have h := build_triples m 1 0 d
    rw [show 1 + 1 + m = m + 1 + 1 from by ring] at h
    convert h using 2; all_goals simp [Nat.add_comm]
  apply stepStar_trans (hb (2 * (m + 1) + 1 + 1))
  -- R3 drain
  apply stepStar_trans (r3_drain (m + 1 + 1) 0 (2 * (m + 1) + 1 + 1 + 2 * m))
  rw [show 0 + 2 * (m + 1 + 1) = 2 * m + 4 from by ring,
      show 2 * (m + 1) + 1 + 1 + 2 * m = 4 * m + 4 from by ring]; finish

-- Even transition: C(2m+2) →⁺ C(2m+3)
theorem main_even (m : ℕ) :
    ⟨0, 0, 2 * m + 4, 4 * m + 4, 0⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 2 * m + 5, 4 * m + 6, 0⟩ := by
  -- First R4 step to establish stepPlus
  rw [show 4 * m + 4 = 2 * (2 * m + 1) + 2 from by ring,
      show 2 * m + 4 = (2 * m + 3) + 1 from by ring]
  step fm
  -- Remaining R4 steps
  apply stepStar_trans (r4_drain (2 * m + 1) ((2 * m + 3) + 1) 1)
  rw [show 1 + (2 * m + 1) = 2 * m + 2 from by ring]
  -- R5
  rw [show (2 * m + 3 : ℕ) + 1 = (2 * m + 3) + 1 from by ring]
  step fm
  -- R2
  rw [show 2 * m + 2 + 1 = (2 * m + 2) + 1 from by ring]
  step fm
  -- Chew×(m+1): (0, 2, 2m+3, 0, 2m+2) → (m+1, 2, 1, 2(m+1), m+1)
  rw [show 2 * m + 3 = 1 + 2 * (m + 1) from by ring,
      show 2 * m + 2 = (m + 1) + (m + 1) from by ring]
  apply stepStar_trans (chew_triples (m + 1) 0 1 0 (m + 1))
  rw [show 0 + (m + 1) = m + 1 from by ring, show 0 + 2 * (m + 1) = 2 * (m + 1) from by ring]
  -- R1: (m+1, 2, 1, 2(m+1), m+1) → (m+2, 1, 0, 2(m+1)+1, m+1)
  step fm
  -- R2×(m+1): (m+2, 1, 0, 2(m+1)+1, m+1) → (1, 2m+3, 0, 2(m+1)+1, 0)
  rw [show m + 1 + 1 = 1 + (m + 1) from by ring]
  apply stepStar_trans (r2_drain (a := 1) (m + 1) 1 (2 * (m + 1) + 1))
  rw [show 1 + 2 * (m + 1) = 2 * m + 3 from by ring]
  -- R3: (1, 2m+3, 0, 2(m+1)+1, 0) → (0, 2m+3, 2, 2(m+1)+1, 0)
  step fm
  -- R1, R1
  rw [show 2 * m + 3 = 2 * m + 1 + 1 + 1 from by ring]
  step fm; step fm
  -- Build×m: (2, 2m+1, 0, d, 0) → (m+2, 1, 0, d+2m, 0)
  have hb : ∀ d, ⟨(2 : ℕ), 2 * m + 1, 0, d, 0⟩ [fm]⊢* ⟨m + 1 + 1, 1, 0, d + 2 * m, 0⟩ := by
    intro d
    have h := build_triples m 1 1 d
    rw [show 1 + 1 + m = m + 1 + 1 from by ring] at h
    convert h using 2; all_goals simp [Nat.add_comm]
  apply stepStar_trans (hb (2 * (m + 1) + 1 + 1 + 1))
  -- R3: (m+2, 1, 0, ..., 0) → (m+1, 1, 2, ..., 0)
  step fm
  -- R1: (m+1, 1, 2, ..., 0) → (m+2, 0, 1, ..., 0)
  step fm
  -- R3 drain
  apply stepStar_trans (r3_drain (m + 1 + 1) 1 (2 * (m + 1) + 1 + 1 + 1 + 2 * m + 1))
  rw [show 1 + 2 * (m + 1 + 1) = 2 * m + 5 from by ring,
      show 2 * (m + 1) + 1 + 1 + 1 + 2 * m + 1 = 4 * m + 6 from by ring]; finish

-- Unified main transition
theorem main_trans (k : ℕ) :
    ⟨0, 0, (k + 1) + 2, 2 * (k + 1), 0⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, (k + 2) + 2, 2 * (k + 2), 0⟩ := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m + 1 + 2 = 2 * m + 3 from by ring,
        show 2 * (m + m + 1) = 4 * m + 2 from by ring,
        show m + m + 2 + 2 = 2 * m + 4 from by ring,
        show 2 * (m + m + 2) = 4 * m + 4 from by ring]
    exact main_odd m
  · subst hm
    rw [show 2 * m + 1 + 1 + 2 = 2 * m + 4 from by ring,
        show 2 * (2 * m + 1 + 1) = 4 * m + 4 from by ring,
        show 2 * m + 1 + 2 + 2 = 2 * m + 5 from by ring,
        show 2 * (2 * m + 1 + 2) = 4 * m + 6 from by ring]
    exact main_even m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 2, 0⟩)
  · unfold c₀; execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, (n + 1) + 2, 2 * (n + 1), 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_289
