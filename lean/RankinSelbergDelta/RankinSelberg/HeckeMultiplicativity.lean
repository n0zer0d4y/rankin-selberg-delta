import Mathlib
import RankinSelbergDelta.RankinSelberg.HeckeEuler

/-!
# Multiplicativity of Hecke eigenvalues from the prime relations

If for every prime `p` there is `e` with `a(pn) + [p ∣ n] p^{k−1} a(n/p) = e · a(n)` for all `n`
(what `T_p f = e f` and the coefficient formula give), then `a` satisfies all four fields of
`IsHeckeEigenCoeffs`, coprime multiplicativity included. No composite Hecke operator is needed.
-/

namespace RankinSelbergDelta.Hecke

/-- The single-prime Hecke relation with eigenvalue `a p`, from the existential form at `n = 1`. -/
lemma hecke_relation_of_exists {a : ℕ → ℂ} (h1 : a 1 = 1) {p : ℕ} (hpp : p.Prime) {cp : ℂ}
    (h : ∃ e : ℂ, ∀ n : ℕ, a (p * n) + (if p ∣ n then cp * a (n / p) else 0) = e * a n) :
    ∀ n : ℕ, a (p * n) + (if p ∣ n then cp * a (n / p) else 0) = a p * a n := by
  obtain ⟨e, he⟩ := h
  have hp1 : ¬ p ∣ 1 := fun h => hpp.one_lt.ne' (Nat.dvd_one.mp h)
  have hap : a p = e := by
    have := he 1
    rwa [mul_one, if_neg hp1, add_zero, h1, mul_one] at this
  intro n
  rw [he n, hap]

/-- **Coprime multiplicativity from the single-prime relations.** If `a 0 = 0`, `a 1 = 1` and
for every prime `p` and every `n`, `a(pn) + [p ∣ n] c_p a(n/p) = a(p) a(n)`, then
`a(mn) = a(m) a(n)` whenever `m` and `n` are coprime. Induction on `m`: write `m = p m₁`, apply
the relation at `m₁ n` and at `m₁`, and use the induction hypothesis at `m₁` (and at `m₁/p`
when `p ∣ m₁`); the two bracket terms agree because `p ∤ n`. -/
theorem mul_coprime_of_hecke_relation (a : ℕ → ℂ) (c : ℕ → ℂ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hrel : ∀ p : ℕ, p.Prime → ∀ n : ℕ,
      a (p * n) + (if p ∣ n then c p * a (n / p) else 0) = a p * a n) :
    ∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n hmn
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp [h0]
    · simp [h1]
  · obtain ⟨p, hpp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
    obtain ⟨m₁, rfl⟩ := hpm
    have hp2 := hpp.two_le
    have hm₁ : m₁ ≠ 0 := by rintro rfl; omega
    have hm₁pos : 0 < m₁ := Nat.pos_of_ne_zero hm₁
    have hm₁lt : m₁ < p * m₁ := by nlinarith
    have hpn : ¬ p ∣ n :=
      (Nat.Prime.coprime_iff_not_dvd hpp).mp (Nat.Coprime.coprime_dvd_left (dvd_mul_right p m₁) hmn)
    have hm₁n : Nat.Coprime m₁ n := Nat.Coprime.coprime_dvd_left (dvd_mul_left m₁ p) hmn
    have hIH₁ : a (m₁ * n) = a m₁ * a n := ih m₁ hm₁lt n hm₁n
    have hA := hrel p hpp (m₁ * n)
    have hB := hrel p hpp m₁
    rw [mul_assoc]
    by_cases hdvd : p ∣ m₁
    · obtain ⟨m₂, rfl⟩ := hdvd
      have hm₂pos : 0 < m₂ := by
        rcases Nat.eq_zero_or_pos m₂ with rfl | h
        · simp at hm₁
        · exact h
      have hm₂lt : m₂ < p * (p * m₂) := by nlinarith
      have hm₂n : Nat.Coprime m₂ n := Nat.Coprime.coprime_dvd_left (dvd_mul_left m₂ p) hm₁n
      have hIH₂ : a (m₂ * n) = a m₂ * a n := ih m₂ hm₂lt n hm₂n
      have hd1 : p ∣ p * m₂ * n := ⟨m₂ * n, by ring⟩
      have hq1 : p * m₂ * n / p = m₂ * n := by
        rw [mul_assoc, Nat.mul_div_cancel_left _ hpp.pos]
      have hq2 : p * m₂ / p = m₂ := Nat.mul_div_cancel_left _ hpp.pos
      rw [if_pos hd1, hq1] at hA
      rw [if_pos (dvd_mul_right p m₂), hq2] at hB
      linear_combination hA - a n * hB + a p * hIH₁ - c p * hIH₂
    · have hnd : ¬ p ∣ m₁ * n := fun h => (hpp.dvd_mul.mp h).elim hdvd hpn
      rw [if_neg hnd, add_zero] at hA
      rw [if_neg hdvd, add_zero] at hB
      linear_combination hA - a n * hB + a p * hIH₁

/-- The prime-power recursion from the single-prime relation at `n = p^{r+1}`. -/
lemma recursion_of_hecke_relation (a : ℕ → ℂ) (k : ℤ) {p : ℕ} (hpp : p.Prime)
    (hrel : ∀ n : ℕ,
      a (p * n) + (if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0) = a p * a n) (r : ℕ) :
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) * a (p ^ r) := by
  have hdiv : p ^ (r + 1) / p = p ^ r := by rw [pow_succ]; exact Nat.mul_div_cancel _ hpp.pos
  have hmul : p * p ^ (r + 1) = p ^ (r + 2) := by rw [← pow_succ']
  have hn := hrel (p ^ (r + 1))
  rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero r)), hdiv, hmul] at hn
  linear_combination hn

/-- **`IsHeckeEigenCoeffs` from the single-prime eigen-relations alone**: given `a 0 = 0`,
`a 1 = 1`, and for every prime `p` an eigenvalue `e_p` with
`a(pn) + [p ∣ n] p^{k−1} a(n/p) = e_p a(n)` for all `n` (which is exactly what
`T_p f = e_p f` plus the `T_p` coefficient formula gives), all four fields follow. -/
theorem isHeckeEigenCoeffs_of_relation (a : ℕ → ℂ) (k : ℤ) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hrel : ∀ p : ℕ, p.Prime → ∃ e : ℂ, ∀ n : ℕ,
      a (p * n) + (if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0) = e * a n) :
    RankinSelbergDelta.RankinSelberg.IsHeckeEigenCoeffs a k := by
  have hrel' : ∀ p : ℕ, p.Prime → ∀ n : ℕ,
      a (p * n) + (if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0) = a p * a n :=
    fun p hpp => hecke_relation_of_exists h1 hpp (hrel p hpp)
  refine ⟨h0, h1, ?_, ?_⟩
  · exact mul_coprime_of_hecke_relation a (fun p => (p : ℂ) ^ (k - 1)) h0 h1 hrel'
  · intro p r hpp
    exact recursion_of_hecke_relation a k hpp (hrel' p hpp) r

end RankinSelbergDelta.Hecke
