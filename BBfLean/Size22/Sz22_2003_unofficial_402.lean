import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #402: [225/14, 7/33, 20/3, 11/5, 3/2]

Vector representation:
```
-1  2  2 -1  0
 0 -1  0  1 -1
 2 -1  1  0  0
 0  0 -1  0  1
-1  1  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_402

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c+2, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: move c to e
theorem c_to_e : ∀ k a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a e; simp; exists 0
  | succ k ih =>
    intro a e
    step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- R3 repeated: drain b
theorem r3_chain : ∀ b a c, ⟨a, b, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * b, 0, c + b, 0, 0⟩ := by
  intro b; induction b with
  | zero => intro a c; simp; exists 0
  | succ b ih =>
    intro a c
    step fm
    apply stepStar_trans (ih (a + 2) (c + 1))
    ring_nf; finish

-- R1+R2 pair
theorem r1_r2_step (a b c e : ℕ) :
    ⟨a+1, b, c, 1, e+1⟩ [fm]⊢* ⟨a, b+1, c+2, 1, e⟩ := by
  step fm; step fm; finish

-- R1/R2 alternation: k pairs
theorem inner_loop : ∀ k a b c e,
    ⟨a + k, b, c, 1, e + k⟩ [fm]⊢* ⟨a, b + k, c + 2 * k, 1, e⟩ := by
  intro k; induction k with
  | zero => intro a b c e; simp; exists 0
  | succ k ih =>
    intro a b c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans (r1_r2_step (a + k) b c (e + k))
    apply stepStar_trans (ih a (b + 1) (c + 2) e)
    ring_nf; finish

-- R2 repeated: drain
theorem r2_drain : ∀ j b c d e,
    ⟨0, b + j, c, d, e + j⟩ [fm]⊢* ⟨0, b, c, d + j, e⟩ := by
  intro j; induction j with
  | zero => intro b c d e; simp; exists 0
  | succ j ih =>
    intro b c d e
    rw [show b + (j + 1) = (b + j) + 1 from by ring,
        show e + (j + 1) = (e + j) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b c (d + 1) e)
    ring_nf; finish

-- End phase by induction on d
theorem end_phase : ∀ d a b c, (0 < a + b ∨ d = 0) →
    ⟨a, b, c, d, 0⟩ [fm]⊢* ⟨a + 2 * b + 3 * d, 0, c + b + 4 * d, 0, 0⟩ := by
  intro d; induction d with
  | zero =>
    intro a b c _; simp; exact r3_chain b a c
  | succ d ih =>
    intro a b c hab
    match a, b with
    | a + 1, b =>
      step fm
      apply stepStar_trans (ih a (b + 2) (c + 2) (by omega))
      ring_nf; finish
    | 0, b + 1 =>
      step fm; step fm
      apply stepStar_trans (ih 1 (b + 2) (c + 3) (by omega))
      ring_nf; finish
    | 0, 0 => simp at hab

-- Core scramble case 1: e ≤ a. From (a-e+1+e, 0, 0, 1, 0+e) via inner_loop e
theorem scramble_ge (a e : ℕ) (h : e ≤ a) :
    ⟨a + 1, 0, 0, 1, e⟩ [fm]⊢* ⟨a + e + 4, 0, 3 * e + 4, 0, 0⟩ := by
  have h1 := inner_loop e (a + 1 - e) 0 0 0
  rw [show a + 1 - e + e = a + 1 from by omega] at h1
  simp at h1
  apply stepStar_trans h1
  have h2 := end_phase 1 (a + 1 - e) e (2 * e) (by omega)
  have h3 : a + 1 - e + 2 * e + 3 * 1 = a + e + 4 := by omega
  have h4 : 2 * e + e + 4 * 1 = 3 * e + 4 := by ring
  rw [h3, h4] at h2; exact h2

-- Core scramble case 2: e > a. From (0+(a+1), 0, 0, 1, (e-a-1)+(a+1)) via inner_loop (a+1)
theorem scramble_lt (a e : ℕ) (h1 : a < e) (h2 : e ≤ 2 * a + 1) :
    ⟨a + 1, 0, 0, 1, e⟩ [fm]⊢* ⟨a + e + 4, 0, 3 * e + 4, 0, 0⟩ := by
  have h3 := inner_loop (a + 1) 0 0 0 (e - a - 1)
  rw [show e - a - 1 + (a + 1) = e from by omega] at h3
  simp at h3
  apply stepStar_trans h3
  -- State: (0, a+1, 2*(a+1), 1, e-a-1)
  -- We have a < e, e ≤ 2a+2, so e-a-1 ≤ a+1
  -- After inner_loop: (0, a+1, 2(a+1), 1, e-a-1)
  -- Want to apply r2_drain. Need to rewrite carefully.
  -- r2_drain (e-a-1) gives: (0, (2a+2-e)+(e-a-1), ..., 1, 0+(e-a-1)) ⊢* (0, 2a+2-e, ..., 1+(e-a-1), 0)
  have hle1 : e - (a + 1) ≤ a + 1 := by omega
  have h4 := r2_drain (e - (a + 1)) (2 * a + 2 - e) (2 * (a + 1)) 1 0
  have h4a : 2 * a + 2 - e + (e - (a + 1)) = a + 1 := by omega
  have h4b : 0 + (e - (a + 1)) = e - (a + 1) := by omega
  rw [h4a, h4b] at h4
  have h4' : ⟨0, a + 1, 2 * (a + 1), 1, e - (a + 1)⟩ [fm]⊢*
      ⟨0, 2 * a + 2 - e, 2 * (a + 1), 1 + (e - (a + 1)), 0⟩ := h4
  -- e - a - 1 = e - (a + 1)
  have he_eq : e - a - 1 = e - (a + 1) := by omega
  rw [he_eq]
  apply stepStar_trans h4'
  -- State: (0, 2a+2-e, 2(a+1), 1+(e-(a+1)), 0) = (0, 2a+2-e, 2a+2, e-a, 0)
  have h5 := end_phase (1 + (e - (a + 1))) 0 (2 * a + 2 - e) (2 * (a + 1)) (by omega)
  have h6 : 0 + 2 * (2 * a + 2 - e) + 3 * (1 + (e - (a + 1))) = a + e + 4 := by omega
  have h7 : 2 * (a + 1) + (2 * a + 2 - e) + 4 * (1 + (e - (a + 1))) = 3 * e + 4 := by omega
  rw [h6, h7] at h5; exact h5

-- Core scramble combined
theorem scramble_core (a e : ℕ) (h : e ≤ 2 * a + 1) :
    ⟨a + 1, 0, 0, 1, e⟩ [fm]⊢* ⟨a + e + 4, 0, 3 * e + 4, 0, 0⟩ := by
  by_cases hle : e ≤ a
  · exact scramble_ge a e hle
  · exact scramble_lt a e (by omega) (by omega)

-- Full scramble
theorem scramble (A E : ℕ) (hA : A ≥ 2) (hE : E ≥ 1) (hbound : E ≤ 2 * A - 2) :
    ⟨A, 0, 0, 0, E⟩ [fm]⊢⁺ ⟨A + E + 1, 0, 0, 0, 3 * E + 1⟩ := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hA
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hE
  -- A = 2+a, E = 1+e. Need to rewrite to a+2 and e+1 for pattern matching.
  rw [show 2 + a = a + 2 from by ring, show 1 + e = e + 1 from by ring]
  -- R5
  apply step_stepStar_stepPlus
  · show fm ⟨a+2, 0, 0, 0, e+1⟩ = some ⟨a+1, 1, 0, 0, e+1⟩; unfold fm; simp
  -- R2
  apply stepStar_trans (step_stepStar (show fm ⟨a+1, 1, 0, 0, e+1⟩ = some ⟨a+1, 0, 0, 1, e⟩ from by unfold fm; simp))
  -- Core scramble: (a+1, 0, 0, 1, e) ⊢* (a+e+4, 0, 3e+4, 0, 0)
  have hbound' : 1 + e ≤ 2 * a + 2 := by
    have : 2 * (2 + a) = 4 + 2 * a := by ring
    omega
  have hcore : e ≤ 2 * a + 1 := by omega
  apply stepStar_trans (scramble_core a e hcore)
  -- c_to_e: (a+e+4, 0, 3e+4, 0, 0) ⊢* target
  -- Target: (a+2+(e+1)+1, 0, 0, 0, 3*(e+1)+1) which equals (a+e+4, 0, 0, 0, 3e+4)
  rw [show a + 2 + (e + 1) + 1 = a + e + 4 from by ring,
      show 3 * (e + 1) + 1 = 3 * e + 4 from by ring]
  have h := c_to_e (3 * e + 4) (a + e + 4) 0
  simp at h; exact h

-- Base case
theorem base_step : ⟨1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨2, 0, 0, 0, 1⟩ := by
  execute fm 3

def seqE : ℕ → ℕ
  | 0 => 0
  | n + 1 => 3 * seqE n + 1

def seqA : ℕ → ℕ
  | 0 => 1
  | n + 1 => seqA n + seqE n + 1

theorem seqA_pos (n : ℕ) : 0 < seqA n := by
  induction n with
  | zero => simp [seqA]
  | succ n ih => unfold seqA; omega

theorem seqA_ge_two (n : ℕ) (hn : n ≥ 1) : seqA n ≥ 2 := by
  match n with
  | 0 => omega
  | n + 1 => unfold seqA; have := seqA_pos n; omega

theorem seqE_ge_one (n : ℕ) (hn : n ≥ 1) : seqE n ≥ 1 := by
  match n with
  | 0 => omega
  | n + 1 => unfold seqE; omega

theorem seq_bound_aux (n : ℕ) (hn : n ≥ 1) : seqE n + 2 ≤ 2 * seqA n := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold seqE seqA
    match n with
    | 0 => simp [seqA, seqE]
    | n + 1 => have := ih (by omega); omega

theorem seq_bound (n : ℕ) (hn : n ≥ 1) : seqE n ≤ 2 * seqA n - 2 := by
  have := seq_bound_aux n hn; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨2, 0, 0, 0, 1⟩ : Q))
  · exact stepPlus_stepStar base_step
  exact progress_nonhalt_simple (fm := fm)
    (fun n ↦ (⟨seqA (n + 1), 0, 0, 0, seqE (n + 1)⟩ : Q)) 0
    (fun n ↦ ⟨n + 1, by
      show (⟨seqA (n + 1), 0, 0, 0, seqE (n + 1)⟩ : Q) [fm]⊢⁺
        ⟨seqA (n + 1 + 1), 0, 0, 0, seqE (n + 1 + 1)⟩
      have hA : seqA (n + 1 + 1) = seqA (n + 1) + seqE (n + 1) + 1 := by simp [seqA]
      have hE : seqE (n + 1 + 1) = 3 * seqE (n + 1) + 1 := by simp [seqE]
      rw [hA, hE]
      exact scramble (seqA (n + 1)) (seqE (n + 1))
        (seqA_ge_two (n + 1) (by omega))
        (seqE_ge_one (n + 1) (by omega))
        (seq_bound (n + 1) (by omega))⟩)

end Sz22_2003_unofficial_402
