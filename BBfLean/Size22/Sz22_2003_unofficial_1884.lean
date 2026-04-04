import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1884: [9/35, 5/33, 484/5, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 2  0 -1  0  2
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1884

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: transfer e to d.
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1))
    ring_nf; finish

-- R3 chain: (a, 0, c+k, 0, e) →* (a+2k, 0, c, 0, e+2k)
theorem r3_chain : ∀ k, ∀ a c e, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c (e + 2))
    ring_nf; finish

-- Drain round: R5,R1,R2,R1.
theorem drain_round : ⟨a + 1, b, 0, d + 2, 0⟩ [fm]⊢* ⟨a, b + 3, 0, d, 0⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Drain loop: k rounds.
theorem drain_loop : ∀ k, ∀ r a b, ⟨a + k, b, 0, 2 * k + r, 0⟩ [fm]⊢* ⟨a, b + 3 * k, 0, r, 0⟩ := by
  intro k; induction' k with k ih <;> intro r a b
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show 2 * (k + 1) + r = 2 * k + (r + 2) from by ring]
    apply stepStar_trans (ih (r + 2) (a + 1) b)
    apply stepStar_trans (drain_round (a := a) (b := b + 3 * k) (d := r))
    ring_nf; finish

-- End transition for even D: (a+1, b+1, 0, 0, 0) →* (a, b, 2, 0, 0)
theorem end_even : ⟨a + 1, b + 1, 0, 0, 0⟩ [fm]⊢* ⟨a, b, 2, 0, 0⟩ := by
  step fm; step fm; finish

-- End transition for odd D: (a+1, b, 0, 1, 0) →* (a, b+1, 1, 0, 0)
theorem end_odd : ⟨a + 1, b, 0, 1, 0⟩ [fm]⊢* ⟨a, b + 1, 1, 0, 0⟩ := by
  step fm; step fm; step fm; finish

-- Consume: (a, b, c+1, 0, 0) →* (a + 2b + 2(c+1), 0, 0, 0, b + 2(c+1))
-- By strong induction on b.
theorem consume : ∀ B, ∀ a c, ⟨a, B, c + 1, 0, 0⟩ [fm]⊢* ⟨a + 2 * B + 2 * (c + 1), 0, 0, 0, B + 2 * (c + 1)⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih; intro a c
  rcases B with _ | _ | B'
  · -- B=0: R3 chain
    rw [show c + 1 = 0 + (c + 1) from by ring]
    apply stepStar_trans (r3_chain (c + 1) a 0 0)
    ring_nf; finish
  · -- B=1: R3, R2, then R3 chain
    step fm -- R3: (a+2, 1, c, 0, 2)
    step fm -- R2: (a+2, 0, c+1, 0, 1)
    rw [show c + 1 = 0 + (c + 1) from by ring]
    apply stepStar_trans (r3_chain (c + 1) (a + 2) 0 1)
    ring_nf; finish
  · -- B=B'+2: R3, R2, R2, then recurse with B'
    step fm -- R3: (a+2, B'+2, c, 0, 2)
    step fm -- R2: (a+2, B'+1, c+1, 0, 1)
    step fm -- R2: (a+2, B', c+2, 0, 0)
    rw [show c + 2 = (c + 1) + 1 from by ring]
    apply stepStar_trans (ih B' (by omega) (a + 2) (c + 1))
    ring_nf; finish

-- Even D=2m transition (star version).
theorem trans_even_star (m : ℕ) (hm : m ≥ 1) :
    ⟨A + m + 1, 0, 0, 0, 2 * m⟩ [fm]⊢* ⟨A + 6 * m + 2, 0, 0, 0, 3 * m + 3⟩ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- Phase 1: e to d
  apply stepStar_trans
  · rw [show (2 * (m' + 1) : ℕ) = 0 + (2 * m' + 2) from by ring]
    exact e_to_d (2 * m' + 2) 0 (a := A + (m' + 1) + 1) (e := 0)
  -- Phase 2: drain
  apply stepStar_trans
  · rw [show 0 + (2 * m' + 2) = 2 * (m' + 1) + 0 from by ring,
        show A + (m' + 1) + 1 = (A + 1) + (m' + 1) from by ring]
    exact drain_loop (m' + 1) 0 (A + 1) 0
  -- Phase 3: end_even
  apply stepStar_trans
  · rw [show 0 + 3 * (m' + 1) = (3 * m' + 2) + 1 from by ring]
    exact end_even (a := A) (b := 3 * m' + 2)
  -- Phase 4: consume
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (consume (3 * m' + 2) A 1)
  ring_nf; finish

-- Even D=2m transition (plus version).
theorem trans_even (m : ℕ) : ⟨A + m + 1, 0, 0, 0, 2 * m⟩ [fm]⊢⁺ ⟨A + 6 * m + 2, 0, 0, 0, 3 * m + 3⟩ := by
  rcases m with _ | m'
  · -- m=0: D=0: R5, R3
    step fm; step fm; finish
  · -- m >= 1: use the ⊢* lemma and convert via stepStar_stepPlus
    apply stepStar_stepPlus (trans_even_star (m' + 1) (by omega))
    intro h
    simp only [Q, Prod.mk.injEq] at h
    omega

-- Odd D=2m+1 transition (star version).
theorem trans_odd_star (m : ℕ) :
    ⟨A + m + 1, 0, 0, 0, 2 * m + 1⟩ [fm]⊢* ⟨A + 6 * m + 4, 0, 0, 0, 3 * m + 3⟩ := by
  rcases m with _ | m'
  · -- m=0: D=1
    apply stepStar_trans
    · rw [show (1 : ℕ) = 0 + 1 from by ring]
      exact e_to_d 1 0 (a := A + 1) (e := 0)
    apply stepStar_trans (end_odd (a := A) (b := 0))
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (consume 1 A 0)
    ring_nf; finish
  · -- m=m'+1: D=2(m'+1)+1 >= 3
    -- Phase 1: e to d
    apply stepStar_trans
    · rw [show (2 * (m' + 1) + 1 : ℕ) = 0 + (2 * m' + 3) from by ring]
      exact e_to_d (2 * m' + 3) 0 (a := A + (m' + 1) + 1) (e := 0)
    -- Phase 2: drain
    apply stepStar_trans
    · rw [show 0 + (2 * m' + 3) = 2 * (m' + 1) + 1 from by ring,
          show A + (m' + 1) + 1 = (A + 1) + (m' + 1) from by ring]
      exact drain_loop (m' + 1) 1 (A + 1) 0
    -- Phase 3: end_odd
    apply stepStar_trans
    · rw [show 0 + 3 * (m' + 1) = 3 * (m' + 1) from by ring]
      exact end_odd (a := A) (b := 3 * (m' + 1))
    -- Phase 4: consume
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (consume (3 * (m' + 1) + 1) A 0)
    ring_nf; finish

-- Odd D=2m+1 transition (plus version).
theorem trans_odd (m : ℕ) : ⟨A + m + 1, 0, 0, 0, 2 * m + 1⟩ [fm]⊢⁺ ⟨A + 6 * m + 4, 0, 0, 0, 3 * m + 3⟩ := by
  apply stepStar_stepPlus (trans_odd_star m)
  intro h
  simp only [Q, Prod.mk.injEq] at h
  omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 3⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 3 ∧ 2 * a ≥ e + 1)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm; subst hm
      obtain ⟨A, rfl⟩ : ∃ A, a = A + m + 1 := ⟨a - m - 1, by omega⟩
      exact ⟨⟨A + 6 * m + 2, 0, 0, 0, 3 * m + 3⟩,
        ⟨A + 6 * m + 2, 3 * m + 3, rfl, by omega, by omega⟩, trans_even m⟩
    · subst hm
      obtain ⟨A, rfl⟩ : ∃ A, a = A + m + 1 := ⟨a - m - 1, by omega⟩
      exact ⟨⟨A + 6 * m + 4, 0, 0, 0, 3 * m + 3⟩,
        ⟨A + 6 * m + 4, 3 * m + 3, rfl, by omega, by omega⟩, trans_odd m⟩
  · exact ⟨2, 3, rfl, by omega, by omega⟩
