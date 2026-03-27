import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #432: [27/35, 1/33, 50/3, 11/5, 63/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  0  0 -1
 1 -1  2  0  0
 0  0 -1  0  1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_432

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

theorem c_to_e : ∀ k a c e, ⟨a, 0, c+k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem pair_consume : ∀ k a d e, ⟨a+k+1, 0, 0, d, e+2*k⟩ [fm]⊢* ⟨a+1, 0, 0, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; exists 0
  rw [show a + (k + 1) + 1 = (a + k + 1) + 1 from by ring,
      show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
  step fm
  rw [show e + 2 * k + 2 = (e + 2 * k + 1) + 1 from by ring]
  step fm; step fm; apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem b_to_ac : ∀ k a b c, ⟨a, b+k, c, 0, 0⟩ [fm]⊢* ⟨a+k, b, c+2*k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; apply stepStar_trans (ih _ _ _); ring_nf; finish

theorem r3r1r1_loop : ∀ k a b d, ⟨a, b+1, 0, d+2*k, 0⟩ [fm]⊢* ⟨a+k, b+1+5*k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; exists 0
  rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
  step fm
  rw [show d + 2 * k + 2 = (d + 2 * k + 1) + 1 from by ring]
  step fm
  rw [show d + 2 * k + 1 = (d + 2 * k) + 1 from by ring]
  step fm
  rw [show b + 6 = (b + 5) + 1 from by ring]
  apply stepStar_trans (ih _ _ _); ring_nf; finish

-- Tail: (j+1, 0, 0, 2*m, 0) ->* (j+6*m+5, 0, 10*m+9, 0, 0)
-- R5 -> r3r1r1_loop(m) with b=1,d=1 -> R3 -> R1 -> b_to_ac
private theorem tail0e (m j : ℕ) :
    ⟨j+1, 0, 0, 2*m, 0⟩ [fm]⊢* ⟨j+6*m+5, 0, 10*m+9, 0, 0⟩ := by
  step fm -- R5: (j, 2, 0, 2*m+1, 0)
  -- rewrite for r3r1r1_loop: need (j, (1)+1, 0, (1)+2*m, 0)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r3r1r1_loop m j 1 1)
  -- state: (j+m, 1+1+5*m, 0, 1, 0)
  rw [show 1 + 1 + 5 * m = (5 * m + 1) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm -- R3: (j+m+1, 5*m+1, 2, 1, 0) -- but 1 = 0+1
  step fm -- R1: (j+m+1, 5*m+4, 1, 0, 0)
  rw [show 5 * m + 4 = 0 + (5 * m + 4) from by ring,
      show (1 : ℕ) = 0 + 2 * 0 + 1 from by ring]
  apply stepStar_trans (b_to_ac (5*m+4) _ _ _); ring_nf; finish

-- Tail: (j+1, 0, 0, 2*m+1, 0) ->* (j+6*m+8, 0, 10*m+14, 0, 0)
private theorem tail0o (m j : ℕ) :
    ⟨j+1, 0, 0, 2*m+1, 0⟩ [fm]⊢* ⟨j+6*m+8, 0, 10*m+14, 0, 0⟩ := by
  step fm -- R5: (j, 2, 0, 2*m+2, 0)
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 2 * m + 1 + 1 = 0 + 2 * (m + 1) from by ring]
  apply stepStar_trans (r3r1r1_loop (m+1) j 1 0)
  rw [show 1 + 1 + 5 * (m + 1) = 0 + (5 * m + 7) from by ring,
      show (0 : ℕ) = 0 + 2 * 0 from by ring]
  apply stepStar_trans (b_to_ac (5*m+7) _ _ _); ring_nf; finish

-- Tail: (j+1, 0, 0, 0, 1) ->* (j+4, 0, 7, 0, 0)
private theorem tail10 (j : ℕ) :
    ⟨j+1, 0, 0, 0, 1⟩ [fm]⊢* ⟨j+4, 0, 7, 0, 0⟩ := by
  step fm -- R5: (j, 2, 0, 1, 1)
  step fm -- R2: (j, 1, 0, 1, 0)
  step fm -- R3: (j+1, 0, 2, 1, 0)
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm -- R1: (j+1, 3, 1, 0, 0)
  rw [show (3 : ℕ) = 0 + 3 from by ring,
      show (1 : ℕ) = 0 + 2 * 0 + 1 from by ring]
  apply stepStar_trans (b_to_ac 3 _ _ _); ring_nf; finish

-- Tail: (j+1, 0, 0, 2*m+1, 1) ->* (j+6*m+7, 0, 10*m+12, 0, 0)
-- R5 -> R2 -> R3 -> R1 -> R1 -> r3r1r1_loop(m) -> b_to_ac
private theorem tail1o (m j : ℕ) :
    ⟨j+1, 0, 0, 2*m+1, 1⟩ [fm]⊢* ⟨j+6*m+7, 0, 10*m+12, 0, 0⟩ := by
  step fm -- R5: (j, 2, 0, 2*m+2, 1)
  rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring]
  step fm -- R2: (j, 1, 0, 2*m+2, 0)
  step fm -- R3: (j+1, 0, 2, 2*m+2, 0)
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm -- R1: (j+1, 3, 1, 2*m+1, 0)
  rw [show 2 * m + 1 = 2 * m + 0 + 1 from by ring]
  step fm -- R1: (j+1, 6, 0, 2*m, 0)
  rw [show (6 : ℕ) = 5 + 1 from by ring,
      show 2 * m = 0 + 2 * m from by ring]
  apply stepStar_trans (r3r1r1_loop m _ 5 0)
  rw [show 5 + 1 + 5 * m = 0 + (5 * m + 6) from by ring,
      show (0 : ℕ) = 0 + 2 * 0 from by ring]
  apply stepStar_trans (b_to_ac (5*m+6) _ _ _); ring_nf; finish

-- Tail: (j+1, 0, 0, 2*(m+1), 1) ->* (j+6*m+10, 0, 10*m+17, 0, 0)
private theorem tail1e (m j : ℕ) :
    ⟨j+1, 0, 0, 2*(m+1), 1⟩ [fm]⊢* ⟨j+6*m+10, 0, 10*m+17, 0, 0⟩ := by
  step fm -- R5
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring]
  step fm -- R2
  step fm -- R3
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  step fm -- R1
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm -- R1
  rw [show (6 : ℕ) = 5 + 1 from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring]
  apply stepStar_trans (r3r1r1_loop m _ 5 1)
  rw [show 5 + 1 + 5 * m = (5 * m + 5) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  step fm -- R3
  step fm -- R1
  rw [show 5 * m + 8 = 0 + (5 * m + 8) from by ring,
      show (1 : ℕ) = 0 + 2 * 0 + 1 from by ring]
  apply stepStar_trans (b_to_ac (5*m+8) _ _ _); ring_nf; finish

-- Main transitions as ⊢⁺
-- Even c, k even
theorem trans_ee (m j : ℕ) :
    ⟨j+2*m+1, 0, 4*m, 0, 0⟩ [fm]⊢⁺ ⟨j+6*m+5, 0, 10*m+9, 0, 0⟩ := by
  rcases m with _ | m
  · -- m=0: (j+1, 0, 0, 0, 0)
    -- R5 -> R3 -> R1 -> b_to_ac(4) = 7 steps total
    step fm -- R5: (j, 2, 0, 1, 0)
    step fm -- R3: (j+1, 1, 2, 1, 0)
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm -- R1: (j+1, 4, 1, 0, 0)
    rw [show (4 : ℕ) = 0 + 4 from by ring,
        show (1 : ℕ) = 0 + 2 * 0 + 1 from by ring]
    apply stepStar_trans (b_to_ac 4 _ _ _); ring_nf; finish
  · -- m+1
    rw [show 4 * (m + 1) = (4 * m + 3) + 1 from by ring]
    step fm -- R4: first step for ⊢⁺
    rw [show 4 * m + 3 = 0 + (4 * m + 3) from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (c_to_e (4*m+3) _ _ _)
    rw [show j + 2 * (m + 1) + 1 = j + (2 * m + 2) + 1 from by ring,
        show 0 + 1 + (4 * m + 3) = 0 + 2 * (2 * m + 2) from by ring]
    apply stepStar_trans (pair_consume (2*m+2) j 0 0)
    rw [show 0 + (2 * m + 2) = 2 * (m + 1) from by ring]
    apply stepStar_trans (tail0e (m+1) j); ring_nf; finish

-- Even c, k odd
theorem trans_eo (m j : ℕ) :
    ⟨j+2*m+2, 0, 4*m+2, 0, 0⟩ [fm]⊢⁺ ⟨j+6*m+8, 0, 10*m+14, 0, 0⟩ := by
  rw [show 4 * m + 2 = (4 * m + 1) + 1 from by ring]
  step fm
  rw [show 4 * m + 1 = 0 + (4 * m + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (c_to_e (4*m+1) _ _ _)
  rw [show j + 2 * m + 2 = j + (2 * m + 1) + 1 from by ring,
      show 0 + 1 + (4 * m + 1) = 0 + 2 * (2 * m + 1) from by ring]
  apply stepStar_trans (pair_consume (2*m+1) j 0 0)
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  apply stepStar_trans (tail0o m j); ring_nf; finish

-- Odd c, k=0
theorem trans_o0 (j : ℕ) :
    ⟨j+1, 0, 1, 0, 0⟩ [fm]⊢⁺ ⟨j+4, 0, 7, 0, 0⟩ := by
  step fm -- R4
  exact tail10 j

-- Odd c, k+1 odd
theorem trans_oo (m j : ℕ) :
    ⟨j+2*m+2, 0, 4*m+3, 0, 0⟩ [fm]⊢⁺ ⟨j+6*m+7, 0, 10*m+12, 0, 0⟩ := by
  rw [show 4 * m + 3 = (4 * m + 2) + 1 from by ring]
  step fm
  rw [show 4 * m + 2 = 0 + (4 * m + 2) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (c_to_e (4*m+2) _ _ _)
  rw [show j + 2 * m + 2 = j + (2 * m + 1) + 1 from by ring,
      show 0 + 1 + (4 * m + 2) = 1 + 2 * (2 * m + 1) from by ring]
  apply stepStar_trans (pair_consume (2*m+1) j 0 1)
  rw [show 0 + (2 * m + 1) = 2 * m + 1 from by ring]
  apply stepStar_trans (tail1o m j); ring_nf; finish

-- Odd c, k+1 even (k+1 = 2*(m+1))
theorem trans_oe (m j : ℕ) :
    ⟨j+2*m+3, 0, 4*m+5, 0, 0⟩ [fm]⊢⁺ ⟨j+6*m+10, 0, 10*m+17, 0, 0⟩ := by
  rw [show 4 * m + 5 = (4 * m + 4) + 1 from by ring]
  step fm
  rw [show 4 * m + 4 = 0 + (4 * m + 4) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (c_to_e (4*m+4) _ _ _)
  rw [show j + 2 * m + 3 = j + (2 * (m + 1)) + 1 from by ring,
      show 0 + 1 + (4 * m + 4) = 1 + 2 * (2 * (m + 1)) from by ring]
  apply stepStar_trans (pair_consume (2*(m+1)) j 0 1)
  rw [show 0 + 2 * (m + 1) = 2 * (m + 1) from by ring]
  apply stepStar_trans (tail1e m j); ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  unfold c₀
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ j k, q = ⟨j+k+1, 0, 2*k, 0, 0⟩ ∨ q = ⟨j+k+1, 0, 2*k+1, 0, 0⟩)
  · intro q ⟨j, k, hq⟩
    rcases hq with hq | hq
    · -- even case: q = (j+k+1, 0, 2*k, 0, 0)
      subst hq
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- k = 2m
        subst hm
        refine ⟨⟨j+6*m+5, 0, 10*m+9, 0, 0⟩, ⟨j+m, 5*m+4, Or.inr ?_⟩, ?_⟩
        · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp <;> omega
        · have heq : (⟨j + (m + m) + 1, 0, 2 * (m + m), 0, 0⟩ : Q) = ⟨j+2*m+1, 0, 4*m, 0, 0⟩ := by
            refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp <;> omega
          rw [heq]; exact trans_ee m j
      · -- k = 2m+1
        subst hm
        refine ⟨⟨j+6*m+8, 0, 10*m+14, 0, 0⟩, ⟨j+m, 5*m+7, Or.inl ?_⟩, ?_⟩
        · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp <;> omega
        · have heq : (⟨j + (2 * m + 1) + 1, 0, 2 * (2 * m + 1), 0, 0⟩ : Q) = ⟨j+2*m+2, 0, 4*m+2, 0, 0⟩ := by
            refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp <;> omega
          rw [heq]; exact trans_eo m j
    · -- odd case: q = (j+k+1, 0, 2*k+1, 0, 0)
      subst hq
      rcases k with _ | k
      · -- k = 0
        refine ⟨⟨j+4, 0, 7, 0, 0⟩, ⟨j, 3, Or.inr ?_⟩, trans_o0 j⟩
        refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp
      · -- k+1
        rcases Nat.even_or_odd (k+1) with ⟨m, hm⟩ | ⟨m, hm⟩
        · -- k+1 = 2*m, so m >= 1
          rcases m with _ | m
          · omega
          · -- k+1 = 2*(m+1)
            refine ⟨⟨j+6*m+10, 0, 10*m+17, 0, 0⟩, ⟨j+m+1, 5*m+8, Or.inr ?_⟩, ?_⟩
            · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp <;> omega
            · have heq : (⟨j + (k+1) + 1, 0, 2*(k+1)+1, 0, 0⟩ : Q) = ⟨j+2*m+3, 0, 4*m+5, 0, 0⟩ := by
                refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp <;> omega
              rw [heq]; exact trans_oe m j
        · -- k+1 = 2*m+1
          refine ⟨⟨j+6*m+7, 0, 10*m+12, 0, 0⟩, ⟨j+m, 5*m+6, Or.inl ?_⟩, ?_⟩
          · refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp <;> omega
          · have heq : (⟨j + (k+1) + 1, 0, 2*(k+1)+1, 0, 0⟩ : Q) = ⟨j+2*m+2, 0, 4*m+3, 0, 0⟩ := by
              refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp <;> omega
            rw [heq]; exact trans_oo m j
  · exact ⟨0, 0, Or.inl rfl⟩

end Sz22_2003_unofficial_432
