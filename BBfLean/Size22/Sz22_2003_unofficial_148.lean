import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #148: [1/45, 245/3, 3/77, 2/7, 1089/2]

Vector representation:
```
 0 -2 -1  0  0
 0 -1  1  2  0
 0  1  0 -1 -1
 1  0  0 -1  0
-1  2  0  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_148

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+2⟩
  | _ => none

-- Interleave rules 3 and 2: consume e while building c and d
theorem interleave_loop : ∀ k a c d,
    ⟨a, 0, c, d+1, k+1⟩ [fm]⊢* ⟨a, 0, c+k+1, d+k+2, 0⟩ := by
  intro k; induction k with
  | zero =>
    intro a c d; step fm; step fm; finish
  | succ k ih =>
    intro a c d
    step fm; step fm
    apply stepStar_trans (ih a (c+1) (d+1))
    ring_nf; finish

-- Rule 4 repeated: convert d to a
theorem rule4_loop : ∀ k a c,
    ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a+k, 0, c, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; finish
  | succ k ih =>
    intro a c
    step fm
    apply stepStar_trans (ih (a+1) c)
    ring_nf; finish

-- Rules 5 and 1 alternating: convert a and c to e
theorem drain_ac : ∀ k a e,
    ⟨a+k, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e+2*k⟩ := by
  intro k; induction k with
  | zero => intro a e; finish
  | succ k ih =>
    intro a e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (e + 2))
    ring_nf; finish

-- Main transition: one full cycle
theorem main_transition :
    ⟨n+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 0, 2*e+8⟩ := by
  -- Phase A (rule 5): (n+1, 0, 0, 0, e) -> (n, 2, 0, 0, e+2)
  step fm
  -- Phase B1 (rule 2 twice): (n, 2, 0, 0, e+2) -> (n, 0, 2, 4, e+2)
  step fm; step fm
  -- Phase B2 (interleave loop): (n, 0, 2, 4, e+2) -> (n, 0, e+4, e+6, 0)
  rw [show (4 : ℕ) = 3 + 1 from by ring, show e + 2 = (e + 1) + 1 from by ring]
  apply stepStar_trans (interleave_loop (e + 1) n 2 3)
  rw [show 2 + (e + 1) + 1 = e + 4 from by ring,
      show 3 + (e + 1) + 2 = e + 6 from by ring]
  -- Phase C (rule 4 loop): (n, 0, e+4, e+6, 0) -> (n+e+6, 0, e+4, 0, 0)
  apply stepStar_trans (rule4_loop (e + 6) n (e + 4))
  -- Phase D (drain a,c to e): (n+e+6, 0, e+4, 0, 0) -> (n+2, 0, 0, 0, 2e+8)
  rw [show n + (e + 6) = (n + 2) + (e + 4) from by ring]
  apply stepStar_trans (drain_ac (e + 4) (n + 2) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩)
  · finish
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e, q = ⟨n+1, 0, 0, 0, e⟩)
  · intro c ⟨n, e, hq⟩; subst hq
    exact ⟨⟨n+2, 0, 0, 0, 2*e+8⟩, ⟨n+1, 2*e+8, by ring_nf⟩, main_transition⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_148
