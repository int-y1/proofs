import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1066: [5/6, 1/35, 12/55, 847/2, 15/7]

Vector representation:
```
-1 -1  1  0  0
 0  0 -1 -1  0
 2  1 -1  0 -1
-1  0  0  1  2
 0  1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude
-/

namespace Sz22_2003_unofficial_1066

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem r4_drain : ∀ n, ∀ a d e, (⟨a+n, 0, 0, d, e⟩ : Q) [fm]⊢* ⟨a, 0, 0, d+n, e+2*n⟩ := by
  intro n; induction n with
  | zero => intro a d e; ring_nf; exists 0
  | succ n ih =>
    intro a d e
    rw [show a + (n + 1) = (a + n) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 2))
    ring_nf; finish

theorem r5r2_drain_odd : ∀ k, ∀ b e, (⟨0, b, 0, 2*k+1, e⟩ : Q) [fm]⊢* ⟨0, b+k+1, 1, 0, e⟩ := by
  intro k; induction k with
  | zero =>
    intro b e; step fm; ring_nf; finish
  | succ k ih =>
    intro b e
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- R1R1R3 chain: (2, j+1, c, 0, e+j) ⊢* (2, 1, c+j, 0, e)
theorem r1r1r3_chain : ∀ j, ∀ c e, (⟨2, j+1, c, 0, e+j⟩ : Q) [fm]⊢* ⟨2, 1, c+j, 0, e⟩ := by
  intro j; induction j with
  | zero => intro c e; ring_nf; exists 0
  | succ j ih =>
    intro c e
    rw [show (j + 1) + 1 = (j + 1) + 1 from rfl]
    rw [show e + (j + 1) = (e + 1) + j from by ring]
    -- (2, (j+1)+1, c, 0, (e+1)+j)
    -- R1: a+1=2, b+1=(j+1)+1 -> (1, j+1, c+1, 0, (e+1)+j)
    -- But wait, need a+1 >= 1 and b+1 >= 1. The match is ⟨a+1, b+1, c, d, e⟩
    -- So 2 = 1+1, (j+1)+1 = (j+1)+1. But Lean sees 2 as Nat.succ 1, and (j+1)+1.
    -- Actually 2 = 1+1 and (j+1)+1 matches a+1, b+1 with a=1, b=j+1.
    step fm
    -- (1, j+1, c+1, 0, (e+1)+j)
    -- R1: 1 = 0+1, j+1 matches b+1 with b=j.
    -- But we need j+1 to match b+1. Lean sees j+1 = Nat.succ j. ✓
    -- After R1: (0, j, c+2, 0, (e+1)+j)
    step fm
    -- (0, j, c+2, 0, (e+1)+j)
    -- R3: c+2 = (c+1)+1 matches c+1 pattern. (e+1)+j needs to match e+1 pattern.
    -- Lean sees (e+1)+j. For j=0: e+1, matches. For j>0: (e+1)+j = (e+j)+1? No.
    -- (e+1)+j is NOT (e+j)+1 definitionally in Lean for variable j.
    -- Need rewrite: show (e+1)+j = j + (e+1) = ... hmm
    rw [show (e + 1) + j = (e + j) + 1 from by ring]
    -- Now (0, j, (c+1)+1, 0, (e+j)+1)
    step fm
    -- R3: (0+2, j+1, c+1, 0, e+j) = (2, j+1, c+1, 0, e+j)
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

theorem r3r1_drain : ∀ e, ∀ a c, (⟨a, 0, c+2, 0, e⟩ : Q) [fm]⊢* ⟨a+e, 0, c+2, 0, 0⟩ := by
  intro e; induction e with
  | zero => intro a c; ring_nf; exists 0
  | succ e ih =>
    intro a c
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c)
    ring_nf; finish

theorem drain_c : ∀ j, ∀ a, (⟨a+1, 0, j+2, 0, 0⟩ : Q) [fm]⊢* ⟨a+j+2, 0, 1, 0, 0⟩ := by
  intro j; induction j with
  | zero =>
    intro a
    step fm; step fm; step fm; step fm; step fm; step fm
    ring_nf; finish
  | succ j ih =>
    intro a
    rw [show (j + 1) + 2 = (j + 2) + 1 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1))
    ring_nf; finish

theorem main_trans (k : ℕ) : (⟨2*k+1, 0, 0, 0, 2⟩ : Q) [fm]⊢⁺ ⟨4*k+3, 0, 0, 0, 2⟩ := by
  -- Phase 1: first R4 step
  apply step_stepStar_stepPlus
  · show fm ⟨(2*k)+1, 0, 0, 0, 2⟩ = some ⟨2*k, 0, 0, 1, 4⟩; simp [fm]
  -- R4 drain remaining
  apply stepStar_trans
  · have h := r4_drain (2*k) 0 1 4; simp only [Nat.zero_add] at h; exact h
  rw [show 1 + 2 * k = 2 * k + 1 from by ring]
  rw [show 4 + 2 * (2 * k) = 4 * k + 4 from by ring]
  -- Phase 2: R5/R2 drain
  apply stepStar_trans (r5r2_drain_odd k 0 (4*k+4))
  simp only [Nat.zero_add]
  -- Phase 3: R3 step
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨0, k+1, 0+1, 0, (4*k+3)+1⟩ = some ⟨2, k+2, 0, 0, 4*k+3⟩; simp [fm]
  -- Phase 4: R1R1R3 chain: (2, k+2, 0, 0, 4*k+3) ⊢* (2, 1, k+1, 0, 3*k+2)
  -- r1r1r3_chain j c e : (2, j+1, c, 0, e+j) ⊢* (2, 1, c+j, 0, e)
  -- j = k+1, c = 0, e = 3*k+2: j+1 = k+2, e+j = 3*k+2+k+1 = 4*k+3, c+j = k+1. ✓
  apply stepStar_trans
  · rw [show k + 2 = (k + 1) + 1 from by ring]
    rw [show (4 * k + 3 : ℕ) = (3 * k + 2) + (k + 1) from by ring]
    exact r1r1r3_chain (k+1) 0 (3*k+2)
  rw [show 0 + (k + 1) = k + 1 from by ring]
  -- Phase 5: R1 step
  apply stepStar_trans
  · apply step_stepStar
    show fm ⟨1+1, 0+1, k+1, 0, 3*k+2⟩ = some ⟨1, 0, k+1+1, 0, 3*k+2⟩; simp [fm]
  -- Phase 6: R3/R1 drain e
  apply stepStar_trans
  · rw [show k + 1 + 1 = k + 2 from by ring]
    exact r3r1_drain (3*k+2) 1 k
  rw [show 1 + (3 * k + 2) = 3 * k + 3 from by ring]
  -- Phase 7: drain c
  apply stepStar_trans
  · rw [show (3 * k + 3 : ℕ) = (3 * k + 2) + 1 from by ring]
    exact drain_c k (3*k+2)
  rw [show 3 * k + 2 + k + 2 = 4 * k + 4 from by ring]
  -- Phase 8: Final R4/R2
  rw [show (4*k+4 : ℕ) = (4*k+3)+1 from by ring]
  step fm; step fm
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨1, 0, 0, 0, 2⟩ : Q)) (by execute fm 15)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k, q = (⟨2*k+1, 0, 0, 0, 2⟩ : Q))
  · intro c ⟨k, hk⟩
    exact ⟨⟨4*k+3, 0, 0, 0, 2⟩, ⟨2*k+1, by ring_nf⟩, hk ▸ main_trans k⟩
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_1066
