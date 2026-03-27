import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #288: [14/15, 9/22, 1625/2, 11/7, 3/13]

Vector representation:
```
 1 -1 -1  1  0  0
-1  2  0  0 -1  0
-1  0  3  0  0  1
 0  0  0 -1  1  0
 0  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_288

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+3, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

-- R4 chain: convert d to e
theorem r4_chain : ∀ k c d e f,
    ⟨0, 0, c, d + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e + k, f⟩ := by
  intro k; induction k with
  | zero => intro c d e f; simp; exists 0
  | succ k ih =>
    intro c d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show e + (k + 1) = (e + 1) + k from by ring]
    exact ih c d (e + 1) f

-- R3 chain: convert a to c and f (b=0, e=0)
theorem r3_chain : ∀ k c d f,
    ⟨k, 0, c, d, 0, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 3 * k, d, 0, f + k⟩ := by
  intro k; induction k with
  | zero => intro c d f; simp; exists 0
  | succ k ih =>
    intro c d f
    step fm
    apply stepStar_trans (ih (c + 3) d (f + 1))
    ring_nf; finish

-- R3 step with arbitrary b (needs a >= 1)
lemma step_r3_b (a b d f : ℕ) :
    ⟨a + 1, b, 0, d, 0, f⟩ [fm]⊢ ⟨a, b, 3, d, 0, f + 1⟩ := by
  cases b <;> rfl

-- Inner loop: each round does 2 R1's + 1 R2
theorem inner3 : ∀ k a c d e f,
    ⟨a, 2, c + 2 * k, d, e + k, f⟩ [fm]⊢* ⟨a + k, 2, c, d + 2 * k, e, f⟩ := by
  intro k; induction k with
  | zero => intro a c d e f; simp; exists 0
  | succ k ih =>
    intro a c d e f
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) c (d + 2) e f)
    ring_nf; finish

-- R2 drain: convert a,e to b when c=0
lemma r2_step (a b d e f : ℕ) :
    ⟨a + 1, b, 0, d, e + 1, f⟩ [fm]⊢ ⟨a, b + 2, 0, d, e, f⟩ := by
  cases b <;> rfl

theorem r2_drain : ∀ k a b d f,
    ⟨a + k, b, 0, d, k, f⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, 0, f⟩ := by
  intro k; induction k with
  | zero => intro a b d f; simp; exists 0
  | succ k ih =>
    intro a b d f
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    refine stepStar_trans (step_stepStar (r2_step (a + k) b d k f)) ?_
    apply stepStar_trans (ih a (b + 2) d f)
    ring_nf; finish

-- R1+R2 when c=1: (a, 2, 1, d, e+1, f) -> (a, 3, 0, d+1, e, f)
lemma r1_r2_c1 (a d e f : ℕ) :
    ⟨a, 2, 1, d, e + 1, f⟩ [fm]⊢* ⟨a, 3, 0, d + 1, e, f⟩ := by
  step fm; step fm
  ring_nf; finish

-- R3+3R1 step: (a+1, b+3, 0, d, 0, f) -> (a+3, b, 0, d+3, 0, f+1)
lemma drain_step_3 (a b d f : ℕ) :
    ⟨a + 1, b + 3, 0, d, 0, f⟩ [fm]⊢* ⟨a + 3, b, 0, d + 3, 0, f + 1⟩ := by
  refine stepStar_trans (step_stepStar (step_r3_b a (b + 3) d f)) ?_
  step fm; step fm; step fm
  ring_nf; finish

-- Drain chain: (a, b, 0, d, 0, f) ⊢* (0, 0, 3a+2b, d+b, 0, f+a+b)
theorem drain_chain : ∀ b, ∀ a d f, (b ≥ 1 → a ≥ 1) →
    ⟨a, b, 0, d, 0, f⟩ [fm]⊢* ⟨(0 : ℕ), 0, 3 * a + 2 * b, d + b, 0, f + a + b⟩ := by
  intro b; induction' b using Nat.strongRecOn with b IH; intro a d f hab
  rcases b with _ | _ | _ | b'
  · -- b = 0
    have : 3 * a + 2 * 0 = 0 + 3 * a := by ring
    have : d + 0 = d := by ring
    have : f + a + 0 = f + a := by ring
    rw [‹3 * a + 2 * 0 = _›, ‹d + 0 = _›, ‹f + a + 0 = _›]
    exact r3_chain a 0 d f
  · -- b = 1
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    refine stepStar_trans (step_stepStar (step_r3_b a' 1 d f)) ?_
    step fm
    apply stepStar_trans (r3_chain (a' + 1) 2 (d + 1) (f + 1))
    ring_nf; finish
  · -- b = 2
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    refine stepStar_trans (step_stepStar (step_r3_b a' 2 d f)) ?_
    step fm; step fm
    apply stepStar_trans (r3_chain (a' + 2) 1 (d + 2) (f + 1))
    ring_nf; finish
  · -- b = b' + 3
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    apply stepStar_trans (drain_step_3 a' b' d f)
    apply stepStar_trans (IH b' (by omega) (a' + 3) (d + 3) (f + 1) (by omega))
    ring_nf; finish

-- Setup: R5 + R1 + R2
lemma setup (c e f : ℕ) :
    ⟨0, 0, c + 1, 0, e + 1, f + 1⟩ [fm]⊢* ⟨(0 : ℕ), 2, c, 1, e, f⟩ := by
  step fm; step fm; step fm
  ring_nf; finish

-- Middle even: inner3 with c even, then r2_drain
-- a_out = a + j - e, but we express this as A directly to avoid subtraction issues
theorem mid_even (j e A d f : ℕ) (hA : A + e = j) :
    ⟨0, 2, 0 + 2 * j, d, e + j, f⟩ [fm]⊢* ⟨A, 2 + 2 * e, 0, d + 2 * j, 0, f⟩ := by
  apply stepStar_trans (inner3 j 0 0 d e f)
  rw [show (0 : ℕ) + j = A + e from by omega]
  exact r2_drain e A 2 (d + 2 * j) f

-- Middle odd: inner3 with c odd, then R1+R2 + r2_drain
theorem mid_odd (j e A d f : ℕ) (hA : A + e = j) :
    ⟨0, 2, 1 + 2 * j, d, (e + 1) + j, f⟩ [fm]⊢*
    ⟨A, 3 + 2 * e, 0, d + 2 * j + 1, 0, f⟩ := by
  apply stepStar_trans (inner3 j 0 1 d (e + 1) f)
  rw [show (0 : ℕ) + j = j from by ring]
  apply stepStar_trans (r1_r2_c1 j (d + 2 * j) e f)
  show ⟨j, 3, 0, d + 2 * j + 1, e, f⟩ [fm]⊢* _
  rw [show j = A + e from by omega, show d + 2 * (A + e) + 1 = d + 2 * j + 1 from by omega]
  exact r2_drain e A 3 (d + 2 * j + 1) f

-- Bootstrap
theorem bootstrap : c₀ [fm]⊢* ⟨(0 : ℕ), 0, 5, 1, 0, 1⟩ := by
  unfold c₀; execute fm 4

-- Small cycles
theorem cycle_1 : ⟨0, 0, 5, 1, 0, 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 8, 3, 0, 2⟩ := by
  apply step_stepStar_stepPlus (by rfl : fm ⟨0, 0, 5, 1, 0, 1⟩ = some ⟨0, 0, 5, 0, 1, 1⟩)
  execute fm 7

theorem cycle_2 : ⟨0, 0, 8, 3, 0, 2⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 13, 7, 0, 5⟩ := by
  apply step_stepStar_stepPlus (by rfl : fm ⟨0, 0, 8, 3, 0, 2⟩ = some ⟨0, 0, 8, 2, 1, 2⟩)
  execute fm 17

-- Cycle for n = 3: S_3 -> S_4
theorem cycle_3 : ⟨0, 0, 13, 7, 0, 5⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 22, 15, 0, 12⟩ := by
  apply step_stepStar_stepPlus
    (by rfl : fm ⟨0, 0, 13, 7, 0, 5⟩ = some ⟨0, 0, 13, 6, 1, 5⟩)
  rw [show (6 : ℕ) = 0 + 6 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r4_chain 6 13 0 1 5)
  rw [show (0 : ℕ) + 1 + 6 = 7 from by ring]
  rw [show (13 : ℕ) = 12 + 1 from by ring, show (7 : ℕ) = 6 + 1 from by ring,
      show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (setup 12 6 4)
  rw [show (12 : ℕ) = 0 + 2 * 6 from by ring, show (6 : ℕ) = 0 + 6 from by ring]
  apply stepStar_trans (mid_even 6 0 6 1 4 (by ring))
  rw [show 2 + 2 * 0 = 2 from by ring, show 1 + 2 * 6 = 13 from by ring]
  apply stepStar_trans (drain_chain 2 6 13 4 (by omega))
  ring_nf; finish

-- Helper lemma for 2^n parity: 2^n is even for n >= 1
private lemma pow2_even (n : ℕ) (hn : n ≥ 1) : 2 ^ n % 2 = 0 := by
  rcases n with _ | n
  · omega
  · simp [Nat.pow_succ]

-- Helper: 2^n >= n + 7 for n >= 4
private lemma pow2_lb (n : ℕ) (hn : n ≥ 4) : 2 ^ n ≥ n + 7 := by
  rcases n with _ | _ | _ | _ | n
  · omega
  · omega
  · omega
  · omega
  · -- n + 4
    suffices h : 2 ^ (n + 4) ≥ n + 4 + 7 from h
    induction n with
    | zero => decide
    | succ n ih =>
      have h1 : 2 ^ (n + 1 + 4) = 2 * 2 ^ (n + 4) := by
        rw [show n + 1 + 4 = (n + 4) + 1 from by ring, Nat.pow_succ]; ring
      rw [h1]; omega

-- General cycle for n >= 3 using p = 2^n
-- S_n = (0, 0, p+n+2, p-1, 0, p-n)
-- S_{n+1} = (0, 0, 2p+n+3, 2p-1, 0, 2p-(n+1))
theorem cycle_ge4 (n : ℕ) (hn : n ≥ 4) :
    ⟨0, 0, 2^n + n + 2, 2^n - 1, 0, 2^n - n⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 2 * 2^n + n + 3, 2 * 2^n - 1, 0, 2 * 2^n - (n + 1)⟩ := by
  set p := 2^n with hp_def
  have hpn : p ≥ n + 7 := pow2_lb n hn
  have hp_even : p % 2 = 0 := pow2_even n (by omega)
  -- Phase 1: First R4 step then chain
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, p + n + 2, p - 1, 0, p - n⟩ = some ⟨0, 0, p + n + 2, p - 2, 1, p - n⟩
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this]; rfl
  rw [show (p - 2 : ℕ) = 0 + (p - 2) from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r4_chain (p - 2) (p + n + 2) 0 1 (p - n))
  rw [show 0 + 1 + (p - 2) = p - 1 from by omega]
  -- Phase 2: Setup
  rw [show p + n + 2 = (p + n + 1) + 1 from by ring,
      show p - 1 = (p - 2) + 1 from by omega,
      show p - n = (p - n - 1) + 1 from by omega]
  apply stepStar_trans (setup (p + n + 1) (p - 2) (p - n - 1))
  -- Phase 3: Case split on parity of n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = 2k (even): p+n+1 odd, use mid_odd
    -- p + n = p + 2k, which is even. j = (p+n)/2 = p/2 + k.
    -- 2*j = p+n, 2*j+1 = p+n+1.
    -- (e+1)+j = p-2, so e = p-2-j-1 = p-j-3 = p/2-k-3.
    -- A+e = j, so A = j-e = (p/2+k) - (p/2-k-3) = 2k+3 = n+3.
    set j := p / 2 + k with hj_def
    set e := p / 2 - k - 3 with he_def
    have hp2 : p / 2 * 2 = p := by omega
    have hpd2 : p = p / 2 + p / 2 := by omega
    have hj_eq : j = p / 2 + k := rfl
    have hj2 : 2 * j = p + n := by rw [hj_eq, hk]; omega
    have hpn1 : p + n + 1 = 1 + 2 * j := by omega
    have hej1 : (e + 1) + j = p - 2 := by rw [he_def, hj_eq]; omega
    have hAe : (n + 3) + e = j := by rw [he_def, hj_eq, hk]; omega
    rw [hpn1, ← hej1]
    apply stepStar_trans (mid_odd j e (n + 3) 1 (p - n - 1) hAe)
    have h_b : 3 + 2 * e = p - n - 3 := by rw [he_def, hk]; omega
    have h_d : 1 + 2 * j + 1 = p + n + 2 := by omega
    rw [h_b, h_d]
    apply stepStar_trans (drain_chain (p - n - 3) (n + 3) (p + n + 2) (p - n - 1) (by omega))
    have h1 : 3 * (n + 3) + 2 * (p - n - 3) = 2 * p + n + 3 := by omega
    have h2 : (p + n + 2) + (p - n - 3) = 2 * p - 1 := by omega
    have h3 : (p - n - 1) + (n + 3) + (p - n - 3) = 2 * p - (n + 1) := by omega
    rw [h1, h2, h3]; finish
  · -- n = 2k+1 (odd): p+n+1 even, use mid_even
    -- p + n + 1 = p + 2k + 2, which is even. j = (p+n+1)/2 = p/2 + k + 1.
    -- 2*j = p+n+1.
    -- e+j = p-2, so e = p-2-j = p/2-k-3.
    -- A+e = j, so A = j-e = (p/2+k+1)-(p/2-k-3) = 2k+4 = n+3.
    set j := p / 2 + k + 1 with hj_def
    set e := p / 2 - k - 3 with he_def
    have hp2 : p / 2 * 2 = p := by omega
    have hpd2 : p = p / 2 + p / 2 := by omega
    have hj_eq : j = p / 2 + k + 1 := rfl
    have hj2 : 2 * j = p + n + 1 := by rw [hj_eq, hk]; omega
    have hpn1 : p + n + 1 = 0 + 2 * j := by omega
    have hej : e + j = p - 2 := by rw [he_def, hj_eq]; omega
    have hAe : (n + 3) + e = j := by rw [he_def, hj_eq, hk]; omega
    rw [hpn1, ← hej]
    apply stepStar_trans (mid_even j e (n + 3) 1 (p - n - 1) hAe)
    have h_b : 2 + 2 * e = p - n - 3 := by rw [he_def, hk]; omega
    have h_d : 1 + 2 * j = p + n + 2 := by omega
    rw [h_b, h_d]
    apply stepStar_trans (drain_chain (p - n - 3) (n + 3) (p + n + 2) (p - n - 1) (by omega))
    have h1 : 3 * (n + 3) + 2 * (p - n - 3) = 2 * p + n + 3 := by omega
    have h2 : (p + n + 2) + (p - n - 3) = 2 * p - 1 := by omega
    have h3 : (p - n - 1) + (n + 3) + (p - n - 3) = 2 * p - (n + 1) := by omega
    rw [h1, h2, h3]; finish

-- Combined cycle for all n >= 1
theorem cycle (n : ℕ) :
    ⟨0, 0, 2 ^ (n + 1) + (n + 1) + 2, 2 ^ (n + 1) - 1, 0, 2 ^ (n + 1) - (n + 1)⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 2 ^ (n + 2) + (n + 2) + 2, 2 ^ (n + 2) - 1, 0, 2 ^ (n + 2) - (n + 2)⟩ := by
  match n with
  | 0 => exact cycle_1
  | 1 => exact cycle_2
  | 2 => exact cycle_3
  | n + 3 =>
    have h := cycle_ge4 (n + 4) (by omega)
    rw [show 2 * 2 ^ (n + 4) = 2 ^ (n + 5) from by rw [Nat.pow_succ]; ring] at h
    rw [show n + 3 + 1 = n + 4 from by ring, show n + 3 + 2 = n + 5 from by ring]
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts bootstrap
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 2 ^ (n + 1) + (n + 1) + 2, 2 ^ (n + 1) - 1, 0, 2 ^ (n + 1) - (n + 1)⟩) 0
  intro n
  exact ⟨n + 1, cycle n⟩

end Sz22_2003_unofficial_288
