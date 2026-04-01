import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1371: [63/10, 4/77, 363/2, 5/3, 2/11]

Vector representation:
```
-1  2 -1  1  0
 2  0  0 -1 -1
-1  1  0  0  2
 0 -1  1  0  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1371

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4 chain: move b to c
theorem b_to_c : ∀ k b c, ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro b c; exists 0
  | succ k ih =>
    intro b c
    rw [show b + (k + 1) = b + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1))
    ring_nf; finish

-- R3 chain: move a to b, producing e
theorem r3_chain : ∀ k a b e, ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + 2 * k⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = a + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 1) (e + 2))
    ring_nf; finish

-- Drain: (a, b, 0, d, e) ->* (0, b+a+2d, 0, 0, 2a+e+3d)
-- By induction on d.
theorem drain : ∀ d a b e, (e ≥ 1 ∨ a ≥ 1 ∨ d = 0) →
    ⟨a, b, 0, d, e⟩ [fm]⊢* ⟨0, b + a + 2 * d, 0, 0, 2 * a + e + 3 * d⟩ := by
  intro d; induction d with
  | zero =>
    intro a b e _
    rw [show (a : ℕ) = 0 + a from by ring]
    apply stepStar_trans (r3_chain a 0 b e)
    ring_nf; finish
  | succ d ih =>
    intro a b e hcond
    rcases e with _ | e
    · -- e = 0
      rcases a with _ | a
      · exfalso; omega
      · -- a+1, e=0: R3 then R2 then IH(d)
        step fm -- R3: (a, b+1, 0, d+1, 2)
        step fm -- R2: (a+2, b+1, 0, d, 1)
        apply stepStar_trans (ih (a + 2) (b + 1) 1 (by left; omega))
        ring_nf; finish
    · -- e+1: R2 then IH(d)
      step fm -- R2: (a+2, b, 0, d, e)
      apply stepStar_trans (ih (a + 2) b e (by right; left; omega))
      ring_nf; finish

-- Spiral + drain: (0, b, c, d+1, e+1) ->* (0, b+2*(d+1)+3*c, 0, 0, e+1+3*(d+1)+c)
-- By strong induction on c. Requires e+1 >= 1 (always true) and 2*(e+1) >= c+1.
theorem spiral_drain : ∀ c, ∀ b d e, 2 * e ≥ c →
    ⟨0, b, c, d + 1, e + 1⟩ [fm]⊢* ⟨0, b + 2 * (d + 1) + 3 * c, 0, 0, e + 1 + 3 * (d + 1) + c⟩ := by
  intro c; induction c using Nat.strongRecOn with
  | ind c ih_c =>
    intro b d e he
    rcases c with _ | _ | c
    · -- c = 0: drain
      apply stepStar_trans (drain (d + 1) 0 b (e + 1) (by left; omega))
      ring_nf; finish
    · -- c = 1: R2, R1, then drain
      step fm -- R2: (2, b, 1, d, e)
      step fm -- R1: (1, b+2, 0, d+1, e)
      apply stepStar_trans (drain (d + 1) 1 (b + 2) e (by right; left; omega))
      ring_nf; finish
    · -- c + 2: one spiral round (R2, R1, R1), then IH(c)
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      step fm -- R2: (2, b, c+2, d, e'+1)
      step fm -- R1: (1, b+2, c+1, d+1, e'+1)
      step fm -- R1: (0, b+4, c, d+2, e'+1)
      rw [show d + 2 = (d + 1) + 1 from by ring]
      apply stepStar_trans (ih_c c (by omega) (b + 4) (d + 1) e' (by omega))
      ring_nf; finish

-- Main cycle
theorem main_cycle (hE : 2 * E ≥ C + 2) :
    ⟨0, 0, C + 1, 0, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 3 * C + 4, 0, C + E + 3⟩ := by
  obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
  step fm -- R5
  step fm -- R1
  apply stepStar_trans
  · show ⟨0, 2, C, 0 + 1, E' + 1⟩ [fm]⊢*
      ⟨0, 2 + 2 * (0 + 1) + 3 * C, 0, 0, E' + 1 + 3 * (0 + 1) + C⟩
    exact spiral_drain C 2 0 E' (by omega)
  rw [show 2 + 2 * (0 + 1) + 3 * C = 0 + (3 * C + 4) from by ring,
      show E' + 1 + 3 * (0 + 1) + C = C + (E' + 1) + 3 from by ring]
  apply stepStar_trans (b_to_c (3 * C + 4) 0 0 (e := C + (E' + 1) + 3))
  ring_nf; finish

def c_seq : ℕ → ℕ
  | 0 => 0
  | n + 1 => 3 * c_seq n + 3

def e_seq : ℕ → ℕ
  | 0 => 1
  | n + 1 => c_seq n + e_seq n + 2

theorem invariant : ∀ n, 2 * e_seq n ≥ c_seq n + 2 := by
  intro n; induction n with
  | zero => simp [c_seq, e_seq]
  | succ n ih => simp [c_seq, e_seq]; omega

theorem c_seq_succ : c_seq (n + 1) + 1 = 3 * c_seq n + 4 := by
  simp [c_seq]

theorem e_seq_succ : e_seq (n + 1) + 1 = c_seq n + e_seq n + 3 := by
  simp [e_seq]

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, c_seq 0 + 1, 0, e_seq 0 + 1⟩)
  · show ⟨1, 0, 0, 0, 0⟩ [fm]⊢* ⟨0, 0, 0 + 1, 0, 1 + 1⟩
    execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, c_seq n + 1, 0, e_seq n + 1⟩) 0
  intro n; exists n + 1
  rw [c_seq_succ, e_seq_succ]
  exact main_cycle (invariant n)
