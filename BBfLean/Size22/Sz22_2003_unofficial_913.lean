import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #913: [4/15, 3/14, 55/2, 49/5, 50/11]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  1
 0  0 -1  2  0
 1  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_913

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- R3 chain: convert a to c and e
theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c e; simp; exists 0
  | succ k ih =>
    intro a c e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    ring_nf; finish

-- R4 chain: convert c to d
theorem r4_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + 2 * k, e⟩ := by
  intro k; induction k with
  | zero => intro c d e; simp; exists 0
  | succ k ih =>
    intro c d e
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 2) e)
    ring_nf; finish

-- R2 drain: consume d by R2
theorem r2_drain : ∀ k, ∀ a b e, ⟨a + k, b, (0 : ℕ), k, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; simp; exists 0
  | succ k ih =>
    intro a b e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (b + 1) e)
    ring_nf; finish

-- Tail: R3/R1 alternating, consuming b
theorem tail : ∀ b, ∀ a e, ⟨a + 1, b, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢* ⟨a + b + 1, 0, 0, 0, e + b⟩ := by
  intro b; induction b with
  | zero => intro a e; simp; exists 0
  | succ b ih =>
    intro a e
    step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- Round with B=0
theorem round_B0 : ∀ d e, ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 5, e + 1⟩ [fm]⊢* ⟨0, 3, 0, d, e⟩ := by
  intro d e; execute fm 8

-- Round with B=1
theorem round_B1 : ∀ d e, ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), d + 5, e + 1⟩ [fm]⊢* ⟨0, 4, 0, d, e⟩ := by
  intro d e; execute fm 8

-- Round with B>=2
theorem round_Bge2 : ∀ b d e, ⟨(0 : ℕ), b + 2, (0 : ℕ), d + 5, e + 1⟩ [fm]⊢* ⟨0, b + 5, 0, d, e⟩ := by
  intro b d e
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Combined rounds: K+1 rounds starting from B=0
theorem combined_rounds : ∀ K, ∀ d e,
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + 5 * (K + 1), e + (K + 1)⟩ [fm]⊢* ⟨0, 3 * (K + 1), 0, d, e⟩ := by
  intro K; induction K with
  | zero =>
    intro d e
    rw [show d + 5 * 1 = d + 5 from by ring,
        show e + 1 = e + 1 from rfl,
        show (3 : ℕ) * 1 = 3 from by ring]
    exact round_B0 d e
  | succ K ih =>
    intro d e
    rw [show d + 5 * (K + 1 + 1) = (d + 5) + 5 * (K + 1) from by ring,
        show e + (K + 1 + 1) = (e + 1) + (K + 1) from by ring]
    apply stepStar_trans (ih (d + 5) (e + 1))
    show ⟨(0 : ℕ), 3 * (K + 1), (0 : ℕ), d + 5, e + 1⟩ [fm]⊢* ⟨0, 3 * (K + 1 + 1), 0, d, e⟩
    rw [show 3 * (K + 1) = (3 * K + 1) + 2 from by ring,
        show 3 * (K + 1 + 1) = (3 * K + 1) + 5 from by ring]
    exact round_Bge2 (3 * K + 1) d e

-- Terminal + tail + R3 drain for B >= 2, d <= 4
theorem terminal_Bge2 : ∀ d, ∀ b e, d ≤ 4 →
    ⟨(0 : ℕ), b + 2, (0 : ℕ), d, e + 1⟩ [fm]⊢* ⟨0, 0, b + 5, 0, e + 2 * b + d + 5⟩ := by
  intro d b e hd
  step fm; step fm; step fm
  show ⟨5, b, (0 : ℕ), d, e⟩ [fm]⊢* ⟨0, 0, b + 5, 0, e + 2 * b + d + 5⟩
  have h1 : ⟨(5 - d) + d, b, (0 : ℕ), d, e⟩ [fm]⊢* ⟨5 - d, b + d, 0, 0, e⟩ :=
    r2_drain d (5 - d) b e
  rw [show (5 - d) + d = 5 from by omega] at h1
  apply stepStar_trans h1
  rw [show 5 - d = (4 - d) + 1 from by omega]
  apply stepStar_trans (tail (b + d) (4 - d) e)
  rw [show (4 - d) + (b + d) + 1 = b + 5 from by omega,
      show e + (b + d) = e + b + d from by ring]
  rw [show b + 5 = 0 + (b + 5) from by ring]
  apply stepStar_trans (r3_chain (b + 5) 0 0 (e + b + d))
  rw [show 0 + (b + 5) = b + 5 from by ring,
      show (e + b + d) + (b + 5) = e + 2 * b + d + 5 from by ring]
  finish

-- Direct transition for c=1
theorem trans_c1 (e : ℕ) : ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢⁺ ⟨0, 0, 3, 0, e + 3⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (r3_chain 3 0 0 e)
  ring_nf; finish

-- Direct transition for c=2
theorem trans_c2 (e : ℕ) : ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢⁺ ⟨0, 0, 3, 0, e + 5⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  apply stepStar_trans (r2_drain 2 1 0 e)
  apply stepStar_trans (tail 2 0 e)
  show ⟨3, (0 : ℕ), (0 : ℕ), (0 : ℕ), e + 2⟩ [fm]⊢* ⟨0, 0, 3, 0, e + 5⟩
  rw [show (3 : ℕ) = 0 + 3 from by ring]
  apply stepStar_trans (r3_chain 3 0 0 (e + 2))
  ring_nf; finish

-- Combined: R4 chain gives (0,0,c,0,e) ⊢* (0,0,0,2c,e)
-- Then for c >= 3, combined_rounds + terminal gives the transition.

-- General transition for c >= 3
theorem trans_cge3 (c e : ℕ) (hc : c ≥ 3) (he : e ≥ c) :
    ⟨(0 : ℕ), (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢⁺
    ⟨0, 0, 3 * (2 * c / 5) + 3, 0, e + 2 * c⟩ := by
  set M := 2 * c / 5 with hM_def
  set R := 2 * c % 5 with hR_def
  have hM : M ≥ 1 := by omega
  have hR4 : R ≤ 4 := by omega
  have h2c : 2 * c = R + 5 * M := by omega
  have hE : e ≥ M + 1 := by
    have : M < c := by omega
    omega
  -- Phase 1: first R4 step (gives ⊢⁺)
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, c, 0, e⟩ = some ⟨0, 0, c - 1, 2, e⟩
    have : c ≥ 1 := by omega
    rw [show c = (c - 1) + 1 from by omega]
    unfold fm; simp
  -- Phase 1 continued: remaining R4 steps
  have h_r4 := r4_chain (c - 1) 0 2 e
  simp at h_r4
  rw [show 2 + 2 * (c - 1) = 2 * c from by omega] at h_r4
  apply stepStar_trans h_r4
  -- Now at (0, 0, 0, 2c, e)
  -- Phase 2: Combined rounds
  -- Rewrite to match combined_rounds signature
  have h_rounds : ⟨(0 : ℕ), 0, 0, R + 5 * ((M - 1) + 1), (e - M) + ((M - 1) + 1)⟩ [fm]⊢*
      ⟨0, 3 * ((M - 1) + 1), 0, R, e - M⟩ := combined_rounds (M - 1) R (e - M)
  rw [show R + 5 * ((M - 1) + 1) = 2 * c from by omega,
      show (e - M) + ((M - 1) + 1) = e from by omega,
      show 3 * ((M - 1) + 1) = 3 * M from by omega] at h_rounds
  apply stepStar_trans h_rounds
  -- Now at (0, 3*M, 0, R, e-M)
  -- Phase 3: Terminal
  have h_term_raw : ⟨(0 : ℕ), (3 * M - 2) + 2, 0, R, (e - M - 1) + 1⟩ [fm]⊢*
      ⟨0, 0, (3 * M - 2) + 5, 0, (e - M - 1) + 2 * (3 * M - 2) + R + 5⟩ :=
    terminal_Bge2 R (3 * M - 2) (e - M - 1) hR4
  rw [show (3 * M - 2) + 2 = 3 * M from by omega,
      show (e - M - 1) + 1 = e - M from by omega,
      show (3 * M - 2) + 5 = 3 * M + 3 from by omega,
      show (e - M - 1) + 2 * (3 * M - 2) + R + 5 = e + 2 * c from by omega] at h_term_raw
  exact h_term_raw

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c, 0, e⟩ ∧ c ≥ 1 ∧ e ≥ c)
  · intro q ⟨c, e, hq, hc, he⟩; subst hq
    rcases (show c = 1 ∨ c = 2 ∨ c ≥ 3 from by omega) with rfl | rfl | hc3
    · -- c = 1
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      exact ⟨⟨0, 0, 3, 0, e' + 3⟩, ⟨3, e' + 3, rfl, by omega, by omega⟩, trans_c1 e'⟩
    · -- c = 2
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      refine ⟨⟨0, 0, 3, 0, e' + 5⟩, ⟨3, e' + 5, rfl, by omega, by omega⟩, ?_⟩
      exact trans_c2 e'
    · -- c >= 3
      set M := 2 * c / 5
      have hM1 : 2 * c / 5 * 5 ≤ 2 * c := Nat.div_mul_le_self (2 * c) 5
      have hM2 : 5 * M ≤ 2 * c := by rw [Nat.mul_comm]; exact hM1
      have he' : e + 2 * c ≥ 3 * M + 3 := by omega
      exact ⟨⟨0, 0, 3 * M + 3, 0, e + 2 * c⟩,
        ⟨3 * M + 3, e + 2 * c, rfl, by omega, he'⟩, trans_cge3 c e hc3 he⟩
  · exact ⟨1, 1, rfl, by omega, le_refl 1⟩

end Sz22_2003_unofficial_913
