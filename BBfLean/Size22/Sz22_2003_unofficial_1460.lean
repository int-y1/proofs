import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1460: [7/15, 3/77, 242/3, 5/11, 63/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1460

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R3 chain: drains b, increasing a and e.
theorem r3_chain : ∀ k, ∀ a b e,
    (⟨a, b + k, 0, 0, e⟩ : Q) [fm]⊢* ⟨a + k, b, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) b (e + 2))
    ring_nf; finish

-- R4 chain: transfers e to c.
theorem r4_chain : ∀ k, ∀ a c e,
    (⟨a, 0, c, 0, e + k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- R5+R1+R1 chain: drains a and c in pairs.
theorem r5r1r1_chain : ∀ m, ∀ a c d,
    (⟨a + m, 0, c + 2 * m, d, 0⟩ : Q) [fm]⊢* ⟨a, 0, c, d + 3 * m, 0⟩ := by
  intro m; induction' m with m ih <;> intro a c d
  · exists 0
  · rw [show a + (m + 1) = (a + m) + 1 from by ring,
        show c + 2 * (m + 1) = (c + 2 * m) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3))
    ring_nf; finish

-- General chain: from (a, b+1, 0, D, 0), produces (a+b+D+1, 0, 0, 0, 2*b+D+2).
theorem gen_chain : ∀ D, ∀ a b,
    (⟨a, b + 1, 0, D, 0⟩ : Q) [fm]⊢* ⟨a + b + D + 1, 0, 0, 0, 2 * b + D + 2⟩ := by
  intro D; induction D using Nat.strongRecOn with
  | _ D ih =>
  intro a b
  rcases D with _ | _ | D
  · -- D = 0: R3 chain
    have := r3_chain (b + 1) a 0 0
    simp at this
    rw [show a + b + 0 + 1 = a + (b + 1) from by ring,
        show 2 * b + 0 + 2 = 2 * (b + 1) from by ring]
    exact this
  · -- D = 1: R3, R2, then R3 chain
    step fm
    rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    have := r3_chain (b + 1) (a + 1) 0 1
    simp at this
    rw [show a + b + 1 + 1 = (a + 1) + (b + 1) from by ring,
        show 2 * b + 1 + 2 = 1 + 2 * (b + 1) from by ring]
    exact this
  · -- D + 2: R3, R2, R2, then IH
    step fm
    rw [show D + 2 = (D + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih D (by omega) (a + 1) (b + 1))
    ring_nf; finish

-- Combined chain from (a+1, 0, 0, D, 0) to (a+D+3, 0, 0, 0, D+5).
-- R5 step then gen_chain. Strong induction on D to get d in succ form.
theorem full_chain : ∀ D, ∀ a,
    (⟨a + 1, 0, 0, D, 0⟩ : Q) [fm]⊢⁺ ⟨a + D + 3, 0, 0, 0, D + 5⟩ := by
  intro D; induction D using Nat.strongRecOn with
  | _ D ih =>
  intro a
  rcases D with _ | D
  · -- D = 0: R5: (a, 2, 0, 1, 0). Then gen_chain(1, a, 1).
    step fm
    have := gen_chain 1 a 1
    rw [show a + 1 + 1 + 1 = a + 0 + 3 from by ring,
        show 2 * 1 + 1 + 2 = 0 + 5 from by ring] at this
    exact this
  · -- D+1: R5: (a, 2, 0, D+2, 0). Then gen_chain(D+2, a, 1).
    step fm
    have := gen_chain (D + 2) a 1
    rw [show a + 1 + (D + 2) + 1 = a + (D + 1) + 3 from by ring,
        show 2 * 1 + (D + 2) + 2 = (D + 1) + 5 from by ring] at this
    exact this

-- Chain from (a, 0, 0, D+1, 2): R2,R2 then gen_chain, or R2,R3 for D=0.
theorem chain_e2 : ∀ D, ∀ a,
    (⟨a, 0, 0, D + 1, 2⟩ : Q) [fm]⊢* ⟨a + D + 1, 0, 0, 0, D + 3⟩ := by
  intro D; induction D using Nat.strongRecOn with
  | _ D ih =>
  intro a
  rcases D with _ | D
  · -- D = 0: (a, 0, 0, 1, 2). R2: (a, 1, 0, 0, 1). R3: (a+1, 0, 0, 0, 3).
    rw [show (1 : ℕ) = 0 + 1 from rfl, show (2 : ℕ) = 0 + 1 + 1 from rfl]
    step fm; step fm
    ring_nf; finish
  · -- D+1: (a, 0, 0, D+2, 2). R2: (a, 1, 0, D+1, 1). R2: (a, 2, 0, D, 0).
    -- Then gen_chain(D, a, 1).
    rw [show D + 1 + 1 = (D + 1) + 1 from by ring, show (2 : ℕ) = 0 + 1 + 1 from rfl]
    step fm; step fm
    have := gen_chain D a 1
    rw [show a + 1 + D + 1 = a + (D + 1) + 1 from by ring,
        show 2 * 1 + D + 2 = (D + 1) + 3 from by ring] at this
    exact this

-- Even case: (a + m + 1, 0, 2*m, 0, 0) ⊢⁺ (a + 3*m + 3, 0, 3*m + 5, 0, 0)
theorem main_even (a m : ℕ) :
    (⟨a + m + 1, 0, 2 * m, 0, 0⟩ : Q) [fm]⊢⁺ ⟨a + 3 * m + 3, 0, 3 * m + 5, 0, 0⟩ := by
  have phase1 : (⟨a + m + 1, 0, 2 * m, 0, 0⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, 3 * m, 0⟩ := by
    rw [show a + m + 1 = (a + 1) + m from by ring,
        show (2 * m : ℕ) = 0 + 2 * m from by ring,
        show 3 * m = 0 + 3 * m from by ring]
    exact r5r1r1_chain m (a + 1) 0 0
  have phase2 : (⟨a + 1, 0, 0, 3 * m, 0⟩ : Q) [fm]⊢⁺ ⟨a + 3 * m + 3, 0, 0, 0, 3 * m + 5⟩ := by
    have := full_chain (3 * m) a
    rw [show a + 3 * m + 3 = a + 3 * m + 3 from rfl] at this
    exact this
  have phase3 : (⟨a + 3 * m + 3, 0, 0, 0, 3 * m + 5⟩ : Q) [fm]⊢* ⟨a + 3 * m + 3, 0, 3 * m + 5, 0, 0⟩ := by
    rw [show (3 * m + 5 : ℕ) = 0 + (3 * m + 5) from by ring]
    exact r4_chain (3 * m + 5) (a + 3 * m + 3) 0 0
  exact stepStar_stepPlus_stepPlus phase1 (stepPlus_stepStar_stepPlus phase2 phase3)

-- Odd case: (a + m + 1, 0, 2*m+1, 0, 0) ⊢⁺ (a + 3*m + 3, 0, 3*m + 4, 0, 0)
theorem main_odd (a m : ℕ) :
    (⟨a + m + 1, 0, 2 * m + 1, 0, 0⟩ : Q) [fm]⊢⁺ ⟨a + 3 * m + 3, 0, 3 * m + 4, 0, 0⟩ := by
  have phase1 : (⟨a + m + 1, 0, 2 * m + 1, 0, 0⟩ : Q) [fm]⊢* ⟨a + 1, 0, 1, 3 * m, 0⟩ := by
    rw [show a + m + 1 = (a + 1) + m from by ring,
        show 2 * m + 1 = 1 + 2 * m from by ring,
        show 3 * m = 0 + 3 * m from by ring]
    exact r5r1r1_chain m (a + 1) 1 0
  have phase1b : (⟨a + 1, 0, 1, 3 * m, 0⟩ : Q) [fm]⊢⁺ ⟨a + 1, 0, 0, 3 * m + 2, 2⟩ := by
    rcases m with _ | m
    · step fm; step fm; step fm; ring_nf; finish
    · rw [show 3 * (m + 1) = (3 * m + 2) + 1 from by ring]
      step fm
      rw [show (1 : ℕ) = 0 + 1 from rfl,
          show (3 * m + 2) + 1 + 1 = (3 * m + 3) + 1 from by ring]
      step fm; step fm
      ring_nf; finish
  have phase2 : (⟨a + 1, 0, 0, 3 * m + 2, 2⟩ : Q) [fm]⊢* ⟨a + 3 * m + 3, 0, 0, 0, 3 * m + 4⟩ := by
    rw [show 3 * m + 2 = (3 * m + 1) + 1 from by ring,
        show a + 3 * m + 3 = (a + 1) + (3 * m + 1) + 1 from by ring,
        show 3 * m + 4 = (3 * m + 1) + 3 from by ring]
    exact chain_e2 (3 * m + 1) (a + 1)
  have phase3 : (⟨a + 3 * m + 3, 0, 0, 0, 3 * m + 4⟩ : Q) [fm]⊢* ⟨a + 3 * m + 3, 0, 3 * m + 4, 0, 0⟩ := by
    rw [show (3 * m + 4 : ℕ) = 0 + (3 * m + 4) from by ring]
    exact r4_chain (3 * m + 4) (a + 3 * m + 3) 0 0
  exact stepStar_stepPlus_stepPlus phase1
    (stepPlus_stepStar_stepPlus phase1b
      (stepStar_trans phase2 phase3))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 5, 0, 0⟩)
  · execute fm 10
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = ⟨a, 0, c, 0, 0⟩ ∧ a ≥ 1 ∧ 2 * a > c)
  · intro q ⟨a, c, hq, ha, hinv⟩
    subst hq
    rcases Nat.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      have ham : a ≥ m + 1 := by omega
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m + 1 := ⟨a - m - 1, by omega⟩
      refine ⟨⟨a' + 3 * m + 3, 0, 3 * m + 5, 0, 0⟩,
        ⟨a' + 3 * m + 3, 3 * m + 5, rfl, by omega, by omega⟩,
        main_even a' m⟩
    · subst hm
      have ham : a ≥ m + 1 := by omega
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + m + 1 := ⟨a - m - 1, by omega⟩
      refine ⟨⟨a' + 3 * m + 3, 0, 3 * m + 4, 0, 0⟩,
        ⟨a' + 3 * m + 3, 3 * m + 4, rfl, by omega, by omega⟩,
        main_odd a' m⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1460
