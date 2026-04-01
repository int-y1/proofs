import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1458: [7/15, 3/77, 242/3, 5/11, 135/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  3  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1458

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+3, c+1, d, e⟩
  | _ => none

-- R4: move e to c
theorem e_to_c : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

-- R3: drain b into a and e
theorem r3_chain : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (e + 2))
    ring_nf; finish

-- R5+R1x3 chain: k rounds
theorem r5_r1_chain : ∀ k, ∀ a c d, ⟨a + k, 0, c + 2 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3))
    ring_nf; finish

-- End of drain when c=0
theorem drain_end_c0 (a d : ℕ) : ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢* ⟨a, 2, 0, d + 1, 0⟩ := by
  step fm; step fm; finish

-- End of drain when c=1
theorem drain_end_c1 (a d : ℕ) : ⟨a + 1, 0, 1, d, 0⟩ [fm]⊢* ⟨a, 1, 0, d + 2, 0⟩ := by
  step fm; step fm; step fm; finish

-- R3/R2 interleave + R3 chain
theorem r3r2_chain : ∀ D, ∀ A B,
    ⟨A, B + 1, 0, D, 0⟩ [fm]⊢* ⟨A + (B + 1) + D, 0, 0, 0, 2 * (B + 1) + D⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih; intro A B
  rcases D with _ | _ | D
  · apply stepStar_trans (r3_chain (B + 1) A 0)
    ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (r3_chain (B + 1) (A + 1) 1)
    ring_nf; finish
  · step fm; step fm; step fm
    rw [show B + 2 = (B + 1) + 1 from by ring]
    apply stepStar_trans (ih D (by omega) (A + 1) (B + 1))
    ring_nf; finish

-- Full even transition: e = 2*E+2, need a ≥ E+2
theorem full_even (m E : ℕ) :
    ⟨m + E + 2, 0, 0, 0, 2 * E + 2⟩ [fm]⊢* ⟨m + 3 * E + 6, 0, 0, 0, 3 * E + 8⟩ := by
  -- e_to_c
  rw [show (2 * E + 2 : ℕ) = 0 + (2 * E + 2) from by ring]
  apply stepStar_trans (e_to_c (2 * E + 2) (m + E + 2) 0 0)
  -- r5_r1_chain
  rw [show (0 : ℕ) + (2 * E + 2) = 0 + 2 * (E + 1) from by ring,
      show m + E + 2 = (m + 1) + (E + 1) from by ring]
  apply stepStar_trans (r5_r1_chain (E + 1) (m + 1) 0 0)
  -- drain_end_c0
  rw [show (0 : ℕ) + 3 * (E + 1) = 3 * E + 3 from by ring]
  apply stepStar_trans (drain_end_c0 m (3 * E + 3))
  -- r3r2_chain
  show ⟨m, 1 + 1, 0, 3 * E + 3 + 1, 0⟩ [fm]⊢* _
  rw [show 3 * E + 3 + 1 = 3 * E + 4 from by ring]
  apply stepStar_trans (r3r2_chain (3 * E + 4) m 1)
  ring_nf; finish

-- Full odd transition: e = 2*E+1, need a ≥ E+1
theorem full_odd (m E : ℕ) :
    ⟨m + E + 1, 0, 0, 0, 2 * E + 1⟩ [fm]⊢* ⟨m + 3 * E + 3, 0, 0, 0, 3 * E + 4⟩ := by
  rw [show (2 * E + 1 : ℕ) = 0 + (2 * E + 1) from by ring]
  apply stepStar_trans (e_to_c (2 * E + 1) (m + E + 1) 0 0)
  rw [show (0 : ℕ) + (2 * E + 1) = 1 + 2 * E from by ring,
      show m + E + 1 = (m + 1) + E from by ring]
  apply stepStar_trans (r5_r1_chain E (m + 1) 1 0)
  rw [show (0 : ℕ) + 3 * E = 3 * E from by ring]
  apply stepStar_trans (drain_end_c1 m (3 * E))
  show ⟨m, 0 + 1, 0, 3 * E + 2, 0⟩ [fm]⊢* _
  apply stepStar_trans (r3r2_chain (3 * E + 2) m 0)
  ring_nf; finish

-- Wrap ⊢* into ⊢⁺ using the fact that start ≠ end
theorem main_even (m E : ℕ) :
    ⟨m + E + 2, 0, 0, 0, 2 * E + 2⟩ [fm]⊢⁺ ⟨m + 3 * E + 6, 0, 0, 0, 3 * E + 8⟩ :=
  stepStar_stepPlus (full_even m E) (by intro h; have := congr_arg (fun x : Q ↦ x.2.2.2.2) h; simp at this; omega)

theorem main_odd (m E : ℕ) :
    ⟨m + E + 1, 0, 0, 0, 2 * E + 1⟩ [fm]⊢⁺ ⟨m + 3 * E + 3, 0, 0, 0, 3 * E + 4⟩ :=
  stepStar_stepPlus (full_odd m E) (by intro h; have := congr_arg (fun x : Q ↦ x.2.2.2.2) h; simp at this; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩) (by execute fm 6)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ e ≥ 1 ∧ 2 * a ≥ e + 1)
  · intro c ⟨a, e, hq, he, ha⟩; subst hq
    rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨E, rfl⟩ : ∃ E, K = E + 1 := ⟨K - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + E + 2 := ⟨a - E - 2, by omega⟩
      refine ⟨⟨m + 3 * E + 6, 0, 0, 0, 3 * E + 8⟩,
        ⟨m + 3 * E + 6, 3 * E + 8, rfl, by omega, by omega⟩, ?_⟩
      show ⟨m + E + 2, 0, 0, 0, 2 * (E + 1)⟩ [fm]⊢⁺ _
      rw [show 2 * (E + 1) = 2 * E + 2 from by ring]
      exact main_even m E
    · subst hK
      obtain ⟨m, rfl⟩ : ∃ m, a = m + K + 1 := ⟨a - K - 1, by omega⟩
      exact ⟨⟨m + 3 * K + 3, 0, 0, 0, 3 * K + 4⟩,
        ⟨m + 3 * K + 3, 3 * K + 4, rfl, by omega, by omega⟩,
        main_odd m K⟩
  · exact ⟨3, 5, rfl, by omega, by omega⟩
