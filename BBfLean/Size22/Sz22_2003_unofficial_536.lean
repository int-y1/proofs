import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #536: [28/15, 63/22, 65/2, 11/7, 3/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  2  0  1 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_536

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

theorem a_to_cf : ∀ k c f, ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  intro k; induction' k with k ih <;> intro c f
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

theorem d_to_e : ∀ k e, ⟨0, 0, c, k, e, f⟩ [fm]⊢* ⟨0, 0, c, 0, e+k, f⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  step fm; apply stepStar_trans (ih _); ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ c d e,
    ⟨a+1, 0, c+2*k, d, e+k, f⟩ [fm]⊢* ⟨a+3*k+1, 0, c, d+3*k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  apply stepStar_trans (ih (c + 2) d (e + 1))
  rw [show a + 3 * k + 1 = (a + 3 * k) + 1 from by ring]
  step fm; step fm; step fm; ring_nf; finish

theorem r2_chain : ∀ k, ∀ b d, ⟨a+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b+2*k, 0, d+k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih _ _); ring_nf; finish

theorem r3r1_tail : ∀ k, ∀ a d f, ⟨a+1, k, 0, d, 0, f⟩ [fm]⊢* ⟨a+k+1, 0, 0, d+k, 0, f+k⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  rw [show a + 1 = (a + 1) + 0 from by ring]; step fm; step fm
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- Even case: n = 2k, g ≤ 2k+2
theorem trans_even_n (hg : g ≤ 2 * k + 2) :
    ⟨0, 0, 2*k+2, 0, 2*k+g+1, 2*g+2*k+2⟩ [fm]⊢⁺
    ⟨4*k+g+4, 0, 0, 6*k+3*g+4, 0, 4*k+4*g+2⟩ := by
  obtain ⟨j, hj, hj1⟩ : ∃ j, j + (k + g) = 3 * k + 3 ∧ j ≥ 1 :=
    ⟨2*k+3-g, by omega, by omega⟩
  -- R5 + R1
  step fm; step fm
  -- R2+R1+R1 chain: k rounds
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * k + 1 = 1 + 2 * k from by ring,
      show 2 * k + g + 1 = (k + g + 1) + k from by ring]
  apply stepStar_trans (r2r1r1_chain (a := 1) (f := 2*g+2*k+1) k 1 1 (k+g+1))
  -- R2 + R1
  rw [show 1 + 3 * k + 1 = (1 + 3 * k) + 1 from by ring]
  step fm; step fm
  -- State: (3k+3, 1, 0, 3k+3, k+g, 2g+2k+1)
  -- Rewrite 3k+3 to j+(k+g) in both a and d
  rw [show 1 + 3 * k + 2 = 3 * k + 3 from by ring, ← hj]
  -- R2 chain: k+g steps
  apply stepStar_trans (r2_chain (a := j) (f := 2*g+2*k+1) (k+g) 1 (j+(k+g)))
  -- R3+R1 tail
  rw [show 1 + 2 * (k + g) = 2 * (k + g) + 1 from by ring]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hj'_eq : j' + 1 + (k + g) = 3 * k + 3 := hj
  rw [show 4 * k + g + 4 = j' + (2 * (k + g) + 1) + 1 from by omega,
      show 6 * k + 3 * g + 4 = j' + 1 + (k + g) + (k + g) + (2 * (k + g) + 1) from by omega,
      show 4 * k + 4 * g + 2 = 2 * g + 2 * k + 1 + (2 * (k + g) + 1) from by omega]
  exact r3r1_tail (2*(k+g)+1) j' (j'+1+(k+g)+(k+g)) (2*g+2*k+1)

-- Odd case: n = 2k+1, g ≤ 2k+3
theorem trans_odd_n (hg : g ≤ 2 * k + 3) :
    ⟨0, 0, 2*k+3, 0, 2*k+g+2, 2*g+2*k+3⟩ [fm]⊢⁺
    ⟨4*k+g+6, 0, 0, 6*k+3*g+7, 0, 4*k+4*g+4⟩ := by
  obtain ⟨j, hj, hj1⟩ : ∃ j, j + (k + g + 1) = 3 * k + 5 ∧ j ≥ 1 :=
    ⟨2*k+4-g, by omega, by omega⟩
  -- R5 + R1
  step fm; step fm
  -- R2+R1+R1 chain: k+1 rounds
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * k + 2 = 0 + 2 * (k + 1) from by ring,
      show 2 * k + g + 2 = (k + g + 1) + (k + 1) from by ring]
  apply stepStar_trans (r2r1r1_chain (a := 1) (f := 2*g+2*k+2) (k+1) 0 1 (k+g+1))
  -- State: (3k+5, 0, 0, 3k+4, k+g+1, 2g+2k+2)
  -- Rewrite a=3k+5 to j+(k+g+1), keep d=3k+4
  rw [show 1 + 3 * (k + 1) + 1 = 3 * k + 5 from by ring, ← hj,
      show 1 + 3 * (k + 1) = 3 * k + 4 from by ring]
  -- R2 chain: k+g+1 steps
  apply stepStar_trans (r2_chain (a := j) (f := 2*g+2*k+2) (k+g+1) 0 (3*k+4))
  -- R3+R1 tail
  rw [show 0 + 2 * (k + g + 1) = 2 * (k + g + 1) from by ring]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hj'_eq : j' + 1 + (k + g + 1) = 3 * k + 5 := hj
  rw [show 4 * k + g + 6 = j' + 2 * (k + g + 1) + 1 from by omega,
      show 6 * k + 3 * g + 7 = 3 * k + 4 + (k + g + 1) + 2 * (k + g + 1) from by omega,
      show 4 * k + 4 * g + 4 = 2 * g + 2 * k + 2 + 2 * (k + g + 1) from by omega]
  exact r3r1_tail (2*(k+g+1)) j' (3*k+4+(k+g+1)) (2*g+2*k+2)

-- Main transition
theorem main_trans (hg : g ≤ n + 2) :
    ⟨n+2, 0, 0, n+g+1, 0, 2*g⟩ [fm]⊢⁺ ⟨2*n+g+4, 0, 0, 3*n+3*g+4, 0, 2*n+4*g+2⟩ := by
  -- Phase 1: R3 chain
  rw [show n + 2 = 0 + (n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (a_to_cf (n+2) 0 (2*g))
  simp only [Nat.zero_add]
  -- Phase 2: R4 chain
  rw [show 2 * g + (n + 2) = 2 * g + n + 2 from by ring,
      show n + g + 1 = 0 + (n + g + 1) from by ring]
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_e (c := n+2) (f := 2*g+n+2) (n+g+1) 0
    rw [Nat.zero_add] at h
    rw [show 0 + (n + g + 1) = n + g + 1 from by ring]
    exact h
  -- Phase 3: Parity split
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    rw [show 2 * (2 * k) + g + 4 = 4 * k + g + 4 from by ring,
        show 3 * (2 * k) + 3 * g + 4 = 6 * k + 3 * g + 4 from by ring,
        show 2 * (2 * k) + 4 * g + 2 = 4 * k + 4 * g + 2 from by ring]
    exact trans_even_n (by omega)
  · subst hk
    rw [show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show 2 * k + 1 + g + 1 = 2 * k + g + 2 from by ring,
        show 2 * g + (2 * k + 1) + 2 = 2 * g + 2 * k + 3 from by ring,
        show 2 * (2 * k + 1) + g + 4 = 4 * k + g + 6 from by ring,
        show 3 * (2 * k + 1) + 3 * g + 4 = 6 * k + 3 * g + 7 from by ring,
        show 2 * (2 * k + 1) + 4 * g + 2 = 4 * k + 4 * g + 4 from by ring]
    exact trans_odd_n (by omega)

-- Wrap main_trans with explicit constraint preservation for progress_nonhalt
theorem main_trans_with_inv (hg : g ≤ n + 2) :
    ∃ c', (∃ n' g', c' = ⟨n'+2, 0, 0, n'+g'+1, 0, 2*g'⟩ ∧ g' ≤ n'+2) ∧
    (⟨n+2, 0, 0, n+g+1, 0, 2*g⟩ : Q) [fm]⊢⁺ c' := by
  refine ⟨⟨2*n+g+4, 0, 0, 3*n+3*g+4, 0, 2*n+4*g+2⟩, ⟨2*n+g+2, n+2*g+1, ?_, by omega⟩,
    main_trans hg⟩
  rw [show 2 * n + g + 4 = (2 * n + g + 2) + 2 from by omega,
      show 3 * n + 3 * g + 4 = (2 * n + g + 2) + (n + 2 * g + 1) + 1 from by omega,
      show 2 * n + 4 * g + 2 = 2 * (n + 2 * g + 1) from by omega]

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n g, q = ⟨n+2, 0, 0, n+g+1, 0, 2*g⟩ ∧ g ≤ n+2)
  · intro c ⟨n, g, hq, hg⟩; subst hq
    exact main_trans_with_inv hg
  · exact ⟨0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_536
