import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1983: [99/35, 4/5, 25/22, 7/3, 15/2]

Vector representation:
```
 0  2 -1 -1  1
 2  0 -1  0  0
-1  0  2  0 -1
 0 -1  0  1  0
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1983

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 repeated: move b to d.
theorem b_to_d : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- R1R1R3 chain: K rounds, d goes from 2*K to 0.
-- Each round: R1, R1, R3. a decreases by 1, b increases by 4, d decreases by 2, e increases by 1.
theorem r1r1r3_chain : ∀ K, ∀ A B E,
    ⟨A + K, B, 2, 2 * K, E⟩ [fm]⊢*
    ⟨A, B + 4 * K, 2, 0, E + K⟩ := by
  intro K; induction' K with K ih <;> intro A B E
  · exists 0
  · rw [show A + (K + 1) = (A + K) + 1 from by ring,
        show 2 * (K + 1) = 2 * K + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A (B + 4) (E + 1))
    ring_nf; finish

-- R1R1R3 chain for odd d: K rounds, d goes from 2*K+1 to 1.
theorem r1r1r3_chain_odd : ∀ K, ∀ A B E,
    ⟨A + K, B, 2, 2 * K + 1, E⟩ [fm]⊢*
    ⟨A, B + 4 * K, 2, 1, E + K⟩ := by
  intro K; induction' K with K ih <;> intro A B E
  · exists 0
  · rw [show A + (K + 1) = (A + K) + 1 from by ring,
        show 2 * (K + 1) + 1 = (2 * K + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih A (B + 4) (E + 1))
    ring_nf; finish

-- R3R2R2 chain: K rounds of (R3, R2, R2). Each round: a increases by 3, e decreases by 1.
theorem r3r2r2_chain : ∀ K, ∀ A B,
    ⟨A + K + 1, B, 0, 0, K⟩ [fm]⊢*
    ⟨A + 4 * K + 1, B, 0, 0, 0⟩ := by
  intro K; induction' K with K ih <;> intro A B
  · exists 0
  · rw [show A + (K + 1) + 1 = (A + K + 1) + 1 from by ring]
    step fm; step fm; step fm
    rw [show A + K + 1 + 2 + 2 = (A + 4) + K + 1 from by ring]
    apply stepStar_trans (ih (A + 4) B)
    ring_nf; finish

-- Even N transition: N = 2*K.
theorem trans_even : ⟨2 * K + 2, 0, 0, 2 * K + 1, 0⟩ [fm]⊢⁺ ⟨4 * K + 4, 0, 0, 4 * K + 3, 0⟩ := by
  rw [show 2 * K + 2 = (2 * K + 1) + 1 from by ring]
  step fm; step fm; step fm
  conv in (occs := 1) 2 * K => rw [show 2 * K = K + K from by ring]
  apply stepStar_trans (r1r1r3_chain K K 3 0)
  step fm; step fm
  rw [show 0 + K = K from by ring,
      show K + 2 + 2 = 3 + K + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain K 3 (3 + 4 * K))
  rw [show 3 + 4 * K + 1 = 4 * K + 4 from by ring]
  apply stepStar_trans (b_to_d (3 + 4 * K) (4 * K + 4) 0)
  ring_nf; finish

-- Odd N transition: N = 2*K+1.
theorem trans_odd : ⟨2 * K + 3, 0, 0, 2 * K + 2, 0⟩ [fm]⊢⁺ ⟨4 * K + 6, 0, 0, 4 * K + 5, 0⟩ := by
  rw [show 2 * K + 3 = (2 * K + 2) + 1 from by ring]
  step fm; step fm; step fm
  conv in (occs := 1) 2 * K + 1 => rw [show 2 * K + 1 = (K + 1) + K from by ring]
  apply stepStar_trans (r1r1r3_chain_odd K (K + 1) 3 0)
  step fm; step fm
  rw [show 0 + K = K from by ring,
      show K + 1 + 2 = 1 + (K + 1) + 1 from by ring,
      show 3 + 4 * K + 2 = 5 + 4 * K from by ring]
  apply stepStar_trans (r3r2r2_chain (K + 1) 1 (5 + 4 * K))
  rw [show 1 + 4 * (K + 1) + 1 = 4 * K + 6 from by ring]
  apply stepStar_trans (b_to_d (5 + 4 * K) (4 * K + 6) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, n + 1, 0⟩) 0
  intro n
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- n even: n = K + K
    rw [show K + K = 2 * K from by ring] at hK; subst hK
    refine ⟨4 * K + 2, ?_⟩
    show ⟨2 * K + 2, 0, 0, 2 * K + 1, 0⟩ [fm]⊢⁺ ⟨4 * K + 2 + 2, 0, 0, 4 * K + 2 + 1, 0⟩
    rw [show 4 * K + 2 + 2 = 4 * K + 4 from by ring,
        show 4 * K + 2 + 1 = 4 * K + 3 from by ring]
    exact trans_even
  · -- n odd: n = 2*K+1
    subst hK
    refine ⟨4 * K + 4, ?_⟩
    show ⟨2 * K + 1 + 2, 0, 0, 2 * K + 1 + 1, 0⟩ [fm]⊢⁺ ⟨4 * K + 4 + 2, 0, 0, 4 * K + 4 + 1, 0⟩
    rw [show 2 * K + 1 + 2 = 2 * K + 3 from by ring,
        show 2 * K + 1 + 1 = 2 * K + 2 from by ring,
        show 4 * K + 4 + 2 = 4 * K + 6 from by ring,
        show 4 * K + 4 + 1 = 4 * K + 5 from by ring]
    exact trans_odd

end Sz22_2003_unofficial_1983
