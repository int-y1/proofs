import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1500: [7/15, 9/77, 242/3, 5/11, 63/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1500

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R5,R1,R1 chain: each round a-1, c-2, d+3.
theorem drain : ∀ k, ∀ a c d,
    ⟨a + k, (0 : ℕ), c + 2 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; exists 0
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3)); ring_nf; finish

-- R3 drain: b into a and e, with c=0, d=0.
theorem r3_drain : ∀ k, ∀ a e,
    ⟨a, k, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro a e; exists 0
  | succ k ih =>
    intro a e; step fm
    apply stepStar_trans (ih (a + 1) (e + 2)); ring_nf; finish

-- R4 transfer: e to c.
theorem r4_transfer : ∀ k, ∀ a c,
    ⟨a, (0 : ℕ), c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; exists 0
  | succ k ih =>
    intro a c; step fm
    apply stepStar_trans (ih a (c + 1)); ring_nf; finish

-- Combined expand + R3 drain + R4 transfer.
theorem expand_all : ∀ D, ∀ a b,
    ⟨a, b + 1, (0 : ℕ), D, 0⟩ [fm]⊢* ⟨a + b + 1 + 2 * D, 0, 2 * b + 3 * D + 2, 0, 0⟩ := by
  intro D; induction D using Nat.strongRecOn with
  | _ D ih =>
  intro a b
  rcases D with _ | _ | D
  · -- D = 0
    apply stepStar_trans (r3_drain (b + 1) a 0)
    rw [show (0 : ℕ) + 2 * (b + 1) = 2 * b + 2 from by ring]
    apply stepStar_trans (r4_transfer (2 * b + 2) (a + b + 1) 0)
    ring_nf; finish
  · -- D = 1
    step fm; step fm
    apply stepStar_trans (r3_drain (b + 2) (a + 1) 1)
    rw [show (1 : ℕ) + 2 * (b + 2) = 2 * b + 5 from by ring]
    apply stepStar_trans (r4_transfer (2 * b + 5) (a + 1 + (b + 2)) 0)
    ring_nf; finish
  · -- D + 2
    rw [show (D + 1 + 1 : ℕ) = D + 2 from by ring]
    step fm; step fm; step fm
    rw [show b + 4 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih D (by omega) (a + 1) (b + 3))
    ring_nf; finish

-- Bridge c=1: from (a+1, 0, 1, D, 0) to (a+1, 4, 0, D, 0).
theorem bridge_c1 (a : ℕ) : ∀ D,
    ⟨a + 1, (0 : ℕ), 1, D, 0⟩ [fm]⊢* ⟨a + 1, 4, 0, D, 0⟩ := by
  intro D; rcases D with _ | D
  · step fm; step fm; step fm; step fm; step fm; finish
  · rw [show (1 : ℕ) = 0 + 1 from rfl]
    step fm; step fm; step fm; step fm; step fm; ring_nf; finish

-- Bridge c=0: from (a+1, 0, 0, D+1, 0) to (a+1, 5, 0, D, 0).
theorem bridge_c0 (a D : ℕ) :
    ⟨a + 1, (0 : ℕ), 0, D + 1, 0⟩ [fm]⊢* ⟨a + 1, 5, 0, D, 0⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

-- C-odd full transition (⊢*).
theorem trans_c_odd_star (F j : ℕ) :
    ⟨F + j + 1, (0 : ℕ), 2 * j + 1, 0, 0⟩ [fm]⊢*
    ⟨F + 6 * j + 5, 0, 9 * j + 8, 0, 0⟩ := by
  rw [show F + j + 1 = (F + 1) + j from by ring,
      show 2 * j + 1 = 1 + 2 * j from by ring]
  apply stepStar_trans (drain j (F + 1) 1 0)
  rw [show (0 : ℕ) + 3 * j = 3 * j from by ring]
  apply stepStar_trans (bridge_c1 F (3 * j))
  rw [show (4 : ℕ) = 3 + 1 from rfl]
  apply stepStar_trans (expand_all (3 * j) (F + 1) 3)
  ring_nf; finish

-- C-odd transition (⊢⁺).
theorem trans_c_odd (F j : ℕ) :
    ⟨F + j + 1, (0 : ℕ), 2 * j + 1, 0, 0⟩ [fm]⊢⁺
    ⟨F + 6 * j + 5, 0, 9 * j + 8, 0, 0⟩ :=
  stepStar_stepPlus (trans_c_odd_star F j) (by intro h; have := congr_arg (fun q : Q => q.2.2.1) h; simp at this; omega)

-- C-even full transition (⊢*).
theorem trans_c_even_star (G j : ℕ) :
    ⟨G + j + 2, (0 : ℕ), 2 * j + 2, 0, 0⟩ [fm]⊢*
    ⟨G + 6 * j + 10, 0, 9 * j + 16, 0, 0⟩ := by
  rw [show G + j + 2 = (G + 1) + (j + 1) from by ring,
      show 2 * j + 2 = 0 + 2 * (j + 1) from by ring]
  apply stepStar_trans (drain (j + 1) (G + 1) 0 0)
  rw [show (0 : ℕ) + 3 * (j + 1) = 3 * j + 3 from by ring,
      show 3 * j + 3 = (3 * j + 2) + 1 from by ring]
  apply stepStar_trans (bridge_c0 G (3 * j + 2))
  rw [show (5 : ℕ) = 4 + 1 from rfl]
  apply stepStar_trans (expand_all (3 * j + 2) (G + 1) 4)
  ring_nf; finish

-- C-even transition (⊢⁺).
theorem trans_c_even (G j : ℕ) :
    ⟨G + j + 2, (0 : ℕ), 2 * j + 2, 0, 0⟩ [fm]⊢⁺
    ⟨G + 6 * j + 10, 0, 9 * j + 16, 0, 0⟩ :=
  stepStar_stepPlus (trans_c_even_star G j) (by intro h; have := congr_arg (fun q : Q => q.2.2.1) h; simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 7, 0, 0⟩) (by execute fm 13)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c : ℕ, q = ⟨a + 1, 0, c + 1, 0, 0⟩ ∧ 2 * a ≥ c)
  · intro q ⟨a, c, hq, hinv⟩; subst hq
    rcases Nat.even_or_odd c with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- c even: c = j + j = 2*j. C = 2*j+1 odd.
      subst hj
      have haj : a ≥ j := by omega
      refine ⟨⟨a + 5 * j + 5, 0, 9 * j + 8, 0, 0⟩,
        ⟨a + 5 * j + 4, 9 * j + 7, by ring_nf, by omega⟩, ?_⟩
      rw [show a + 1 = (a - j) + j + 1 from by omega,
          show j + j + 1 = 2 * j + 1 from by ring]
      have h := trans_c_odd (a - j) j
      rw [show (a - j) + 6 * j + 5 = a + 5 * j + 5 from by omega] at h
      exact h
    · -- c odd: c = 2*j + 1. C = 2*j+2 even.
      subst hj
      have haj : a ≥ j + 1 := by omega
      refine ⟨⟨a + 5 * j + 9, 0, 9 * j + 16, 0, 0⟩,
        ⟨a + 5 * j + 8, 9 * j + 15, by ring_nf, by omega⟩, ?_⟩
      rw [show a + 1 = (a - j - 1) + j + 2 from by omega,
          show 2 * j + 1 + 1 = 2 * j + 2 from by ring]
      have h := trans_c_even (a - j - 1) j
      rw [show (a - j - 1) + 6 * j + 10 = a + 5 * j + 9 from by omega] at h
      exact h
  · exact ⟨3, 6, rfl, by omega⟩

end Sz22_2003_unofficial_1500
