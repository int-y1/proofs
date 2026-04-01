import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1506: [7/15, 9/77, 44/3, 25/11, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 0  2  0 -1 -1
 2 -1  0  0  1
 0  0  2  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1506

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

-- R4 chain: transfer e to c (doubling).
theorem e_to_c : ∀ k a c e, ⟨a, (0 : ℕ), c, (0 : ℕ), e + k⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · simp; exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 2) e)
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]; exists 0

-- R3R2 interleaved chain: drain d.
theorem r3r2_chain : ∀ k a b d, ⟨a, b + 1, (0 : ℕ), d + k, (0 : ℕ)⟩ [fm]⊢*
    ⟨a + 2 * k, b + k + 1, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 2) (b + 1) d)
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring,
        show b + 1 + k + 1 = b + (k + 1) + 1 from by ring]; exists 0

-- R3 pure drain: drain b when c=d=0.
theorem r3_drain : ∀ j a e, ⟨a, j, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢*
    ⟨a + 2 * j, 0, 0, 0, e + j⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · simp; exists 0
  · step fm
    apply stepStar_trans (ih (a + 2) (e + 1))
    rw [show a + 2 + 2 * j = a + 2 * (j + 1) from by ring,
        show e + 1 + j = e + (j + 1) from by ring]; exists 0

-- c drain: 5-step cycle (R5,R1,R2,R1,R1).
theorem c_drain : ∀ k a c d, ⟨a + k, (0 : ℕ), c + 3 * k, d, (0 : ℕ)⟩ [fm]⊢*
    ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 2))
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) from by ring]; exists 0

-- Phase 3 with e=0: R5, R2, then R3R2 chain, then R3 drain.
theorem phase3_e0 (a d : ℕ) :
    ⟨a + 1, (0 : ℕ), (0 : ℕ), d + 1, (0 : ℕ)⟩ [fm]⊢* ⟨a + 4 * d + 6, 0, 0, 0, d + 3⟩ := by
  step fm; step fm
  show ⟨a, 2 + 1, 0, d, 0⟩ [fm]⊢* _
  rw [show (d : ℕ) = 0 + d from by ring]
  apply stepStar_trans (r3r2_chain d a 2 0)
  rw [show 2 + d + 1 = d + 3 from by ring]
  apply stepStar_trans (r3_drain (d + 3) (a + 2 * d) 0)
  ring_nf; finish

-- Phase 3 with e=1: R2, then R3R2 chain, then R3 drain.
theorem phase3_e1 (a d : ℕ) :
    ⟨a, (0 : ℕ), (0 : ℕ), d + 1, (1 : ℕ)⟩ [fm]⊢* ⟨a + 4 * d + 4, 0, 0, 0, d + 2⟩ := by
  step fm
  show ⟨a, 1 + 1, 0, d, 0⟩ [fm]⊢* _
  rw [show (d : ℕ) = 0 + d from by ring]
  apply stepStar_trans (r3r2_chain d a 1 0)
  rw [show 1 + d + 1 = d + 2 from by ring]
  apply stepStar_trans (r3_drain (d + 2) (a + 2 * d) 0)
  ring_nf; finish

-- Remainder c=1: R5, R1, then phase3_e1.
theorem rem1 (a d : ℕ) :
    ⟨a + 1, (0 : ℕ), (1 : ℕ), d + 1, (0 : ℕ)⟩ [fm]⊢* ⟨a + 4 * d + 8, 0, 0, 0, d + 3⟩ := by
  step fm; step fm
  show ⟨a, 0, 0, (d + 1) + 1, 1⟩ [fm]⊢* _
  apply stepStar_trans (phase3_e1 a (d + 1))
  rw [show a + 4 * (d + 1) + 4 = a + 4 * d + 8 from by ring,
      show (d + 1) + 2 = d + 3 from by ring]; exists 0

-- Remainder c=2: R5, R1, R2, R1, R3, then phase3_e1.
theorem rem2 (a d : ℕ) :
    ⟨a + 1, (0 : ℕ), (2 : ℕ), d + 1, (0 : ℕ)⟩ [fm]⊢* ⟨a + 4 * d + 10, 0, 0, 0, d + 3⟩ := by
  step fm; step fm; step fm; step fm; step fm
  show ⟨a + 2, 0, 0, (d + 1) + 1, 1⟩ [fm]⊢* _
  apply stepStar_trans (phase3_e1 (a + 2) (d + 1))
  rw [show a + 2 + 4 * (d + 1) + 4 = a + 4 * d + 10 from by ring,
      show (d + 1) + 2 = d + 3 from by ring]; exists 0

-- Case e ≡ 0 (mod 3): e = 3(m+1). One R4 step + rest as ⊢*.
theorem trans_mod0 (F m : ℕ) :
    ⟨F + 2 * m + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 3⟩ [fm]⊢⁺
    ⟨F + 16 * m + 18, 0, 0, 0, 4 * m + 6⟩ := by
  rw [show (3 : ℕ) * m + 3 = (3 * m + 2) + 1 from by ring]
  step fm  -- R4: one step for ⊢⁺
  show ⟨F + 2 * m + 3, 0, 2, 0, 3 * m + 2⟩ [fm]⊢* _
  rw [show (3 : ℕ) * m + 2 = 0 + (3 * m + 2) from by ring]
  apply stepStar_trans (e_to_c (3 * m + 2) (F + 2 * m + 3) 2 0)
  rw [show 2 + 2 * (3 * m + 2) = 0 + 3 * (2 * m + 2) from by ring,
      show F + 2 * m + 3 = (F + 1) + (2 * m + 2) from by ring]
  apply stepStar_trans (c_drain (2 * m + 2) (F + 1) 0 0)
  rw [show (0 : ℕ) + 2 * (2 * m + 2) = (4 * m + 3) + 1 from by ring]
  apply stepStar_trans (phase3_e0 F (4 * m + 3))
  rw [show F + 4 * (4 * m + 3) + 6 = F + 16 * m + 18 from by ring,
      show 4 * m + 3 + 3 = 4 * m + 6 from by ring]; exists 0

-- Case e ≡ 1 (mod 3): e = 3n+4. One R4 step + rest as ⊢*.
theorem trans_mod1 (F n : ℕ) :
    ⟨F + 2 * n + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * n + 4⟩ [fm]⊢⁺
    ⟨F + 16 * n + 22, 0, 0, 0, 4 * n + 6⟩ := by
  rw [show (3 : ℕ) * n + 4 = (3 * n + 3) + 1 from by ring]
  step fm  -- R4
  show ⟨F + 2 * n + 3, 0, 2, 0, 3 * n + 3⟩ [fm]⊢* _
  rw [show (3 : ℕ) * n + 3 = 0 + (3 * n + 3) from by ring]
  apply stepStar_trans (e_to_c (3 * n + 3) (F + 2 * n + 3) 2 0)
  rw [show 2 + 2 * (3 * n + 3) = 2 + 3 * (2 * n + 2) from by ring,
      show F + 2 * n + 3 = (F + 1) + (2 * n + 2) from by ring]
  apply stepStar_trans (c_drain (2 * n + 2) (F + 1) 2 0)
  rw [show (0 : ℕ) + 2 * (2 * n + 2) = (4 * n + 3) + 1 from by ring]
  apply stepStar_trans (rem2 F (4 * n + 3))
  rw [show F + 4 * (4 * n + 3) + 10 = F + 16 * n + 22 from by ring,
      show 4 * n + 3 + 3 = 4 * n + 6 from by ring]; exists 0

-- Case e ≡ 2 (mod 3): e = 3m+2. One R4 step + rest as ⊢*.
theorem trans_mod2 (F m : ℕ) :
    ⟨F + 2 * m + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ), 3 * m + 2⟩ [fm]⊢⁺
    ⟨F + 16 * m + 12, 0, 0, 0, 4 * m + 4⟩ := by
  rw [show (3 : ℕ) * m + 2 = (3 * m + 1) + 1 from by ring]
  step fm  -- R4
  show ⟨F + 2 * m + 2, 0, 2, 0, 3 * m + 1⟩ [fm]⊢* _
  rw [show (3 : ℕ) * m + 1 = 0 + (3 * m + 1) from by ring]
  apply stepStar_trans (e_to_c (3 * m + 1) (F + 2 * m + 2) 2 0)
  rw [show 2 + 2 * (3 * m + 1) = 1 + 3 * (2 * m + 1) from by ring,
      show F + 2 * m + 2 = (F + 1) + (2 * m + 1) from by ring]
  apply stepStar_trans (c_drain (2 * m + 1) (F + 1) 1 0)
  rw [show (0 : ℕ) + 2 * (2 * m + 1) = (4 * m + 1) + 1 from by ring]
  apply stepStar_trans (rem1 F (4 * m + 1))
  rw [show F + 4 * (4 * m + 1) + 8 = F + 16 * m + 12 from by ring,
      show 4 * m + 1 + 3 = 4 * m + 4 from by ring]; exists 0

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ e ∧ e ≥ 2)
  · intro c ⟨a, e, hq, ha, he⟩; subst hq
    rcases (show e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 from by omega) with h | h | h
    · obtain ⟨m, hm⟩ : ∃ m, e = 3 * m := ⟨e / 3, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      subst hm
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * m' + 3 := ⟨a - 2 * m' - 3, by omega⟩
      exact ⟨⟨F + 16 * m' + 18, 0, 0, 0, 4 * m' + 6⟩,
        ⟨F + 16 * m' + 18, 4 * m' + 6, rfl, by omega, by omega⟩,
        trans_mod0 F m'⟩
    · obtain ⟨n, hn⟩ : ∃ n, e = 3 * n + 1 := ⟨e / 3, by omega⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      subst hn
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * n' + 3 := ⟨a - 2 * n' - 3, by omega⟩
      exact ⟨⟨F + 16 * n' + 22, 0, 0, 0, 4 * n' + 6⟩,
        ⟨F + 16 * n' + 22, 4 * n' + 6, rfl, by omega, by omega⟩,
        trans_mod1 F n'⟩
    · obtain ⟨m, hm⟩ : ∃ m, e = 3 * m + 2 := ⟨e / 3, by omega⟩
      subst hm
      obtain ⟨F, rfl⟩ : ∃ F, a = F + 2 * m + 2 := ⟨a - 2 * m - 2, by omega⟩
      exact ⟨⟨F + 16 * m + 12, 0, 0, 0, 4 * m + 4⟩,
        ⟨F + 16 * m + 12, 4 * m + 4, rfl, by omega, by omega⟩,
        trans_mod2 F m⟩
  · exact ⟨2, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1506
