import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1403: [7/15, 1/847, 1/3, 78/7, 55/13, 7/2]

Vector representation:
```
 0 -1 -1  1  0  0
 0  0  0 -1 -2  0
 0 -1  0  0  0  0
 1  1  0 -1  0  1
 0  0  1  0  1 -1
-1  0  0  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1403

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e+2, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a+1, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | _ => none

-- R6+R2 drain: each round subtracts 1 from a and 2 from e.
theorem drain : ∀ k a c e, (⟨a + k, 0, c, 0, e + 2 * k, 0⟩ : Q) [fm]⊢* ⟨a, 0, c, 0, e, 0⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c e)
    ring_nf; finish

-- R5 chain: transfer f to c and e.
theorem r5_chain : ∀ k a c e, (⟨a, 0, c, 0, e, k⟩ : Q) [fm]⊢* ⟨a, 0, c + k, 0, e + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    ring_nf; finish

-- R4R1 chain for e=0: from (a, 0, c+k, 1, 0, f) do k rounds of R4,R1.
theorem r4r1_chain_e0 : ∀ k a c f, (⟨a, 0, c + k, 1, 0, f⟩ : Q) [fm]⊢* ⟨a + k, 0, c, 1, 0, f + k⟩ := by
  intro k; induction k with
  | zero => intro a c f; exists 0
  | succ k ih =>
    intro a c f
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (f + 1))
    ring_nf; finish

-- R4R1 chain for e=1: from (a, 0, c+k, 1, 1, f) do k rounds of R4,R1.
theorem r4r1_chain_e1 : ∀ k a c f, (⟨a, 0, c + k, 1, 1, f⟩ : Q) [fm]⊢* ⟨a + k, 0, c, 1, 1, f + k⟩ := by
  intro k; induction k with
  | zero => intro a c f; exists 0
  | succ k ih =>
    intro a c f
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (f + 1))
    ring_nf; finish

-- Build from e=0: (a+1, 0, c, 0, 0, 0) ⊢⁺ (a+c+1, 0, c+1, 0, c+1, 0)
theorem build_e0 (a c : ℕ) :
    (⟨a + 1, 0, c, 0, 0, 0⟩ : Q) [fm]⊢⁺ ⟨a + c + 1, 0, c + 1, 0, c + 1, 0⟩ := by
  -- R6: (a, 0, c, 1, 0, 0)
  step fm
  -- R4R1 chain: c rounds
  rw [show c = 0 + c from by ring]
  apply stepStar_trans (r4r1_chain_e0 c a 0 0)
  rw [show 0 + c = c from by ring]
  -- R4: (a+c+1, 1, 0, 0, 0, c+1)
  step fm
  -- R3: (a+c+1, 0, 0, 0, 0, c+1)
  step fm
  -- R5 chain
  apply stepStar_trans (r5_chain (c + 1) (a + c + 1) 0 0)
  ring_nf; finish

-- Build from e=1: (a+1, 0, c, 0, 1, 0) ⊢⁺ (a+c+1, 0, c+1, 0, c+2, 0)
theorem build_e1 (a c : ℕ) :
    (⟨a + 1, 0, c, 0, 1, 0⟩ : Q) [fm]⊢⁺ ⟨a + c + 1, 0, c + 1, 0, c + 2, 0⟩ := by
  -- R6: (a, 0, c, 1, 1, 0)
  step fm
  -- R4R1 chain: c rounds
  rw [show c = 0 + c from by ring]
  apply stepStar_trans (r4r1_chain_e1 c a 0 0)
  rw [show 0 + c = c from by ring]
  -- R4: (a+c+1, 1, 0, 0, 1, c+1)
  step fm
  -- R3: (a+c+1, 0, 0, 0, 1, c+1)
  step fm
  -- R5 chain
  apply stepStar_trans (r5_chain (c + 1) (a + c + 1) 0 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 1, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c e, q = ⟨a, 0, c, 0, e, 0⟩ ∧ c ≥ 1 ∧ a ≥ e / 2 + 1)
  · intro q ⟨a, c, e, hq, hc, ha⟩
    subst hq
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- Even case: e = 2k
      rw [show k + k = 2 * k from by ring] at hk; subst hk
      have hak : a ≥ k + 1 := by omega
      obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hak
      refine ⟨⟨a' + c + 1, 0, c + 1, 0, c + 1, 0⟩,
        ⟨a' + c + 1, c + 1, c + 1, rfl, by omega, by omega⟩, ?_⟩
      apply stepStar_stepPlus_stepPlus
      · rw [show k + 1 + a' = a' + 1 + k from by ring]
        have h := drain k (a' + 1) c 0
        rw [show 0 + 2 * k = 2 * k from by ring] at h
        exact h
      · exact build_e0 a' c
    · -- Odd case: e = 2k + 1
      subst hk
      have hak : a ≥ k + 1 := by omega
      obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hak
      refine ⟨⟨a' + c + 1, 0, c + 1, 0, c + 2, 0⟩,
        ⟨a' + c + 1, c + 1, c + 2, rfl, by omega, by omega⟩, ?_⟩
      apply stepStar_stepPlus_stepPlus
      · rw [show k + 1 + a' = a' + 1 + k from by ring,
            show 2 * k + 1 = 1 + 2 * k from by ring]
        exact drain k (a' + 1) c 1
      · exact build_e1 a' c
  · exact ⟨1, 1, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1403
