import data.polynomial.erase_lead
import analysis.calculus.deriv
import analysis.asymptotic_equivalent
import equivalent

open polynomial asymptotics filter finset function
open_locale big_operators topological_space asymptotics

section

variables {α β : Type*} [linear_ordered_field α]
variables {l : filter β} {f g : β → α}

lemma tendsto_at_bot_mul_left' {r : α} (hr : r < 0) (hf : tendsto f l at_top) :
  tendsto (λx, r * f x) l at_bot :=
begin
  apply tendsto_at_bot.2 (λb, _),
  filter_upwards [tendsto_at_top.1 hf (b/r)],
  assume x hx,
  simpa [div_le_iff_of_neg' hr] using hx
end

end

variables {α : Type*}

lemma tendsto_abs_at_bot_at_top [linear_ordered_add_comm_group α] :
  tendsto (abs : α → α) at_bot at_top :=
begin
  convert show tendsto (abs ∘ has_neg.neg : α → α) at_bot at_top,
    from tendsto_abs_at_top_at_top.comp tendsto_neg_at_bot_at_top,
  ext,
  simp
end

lemma is_o_pow_pow_at_top_of_lt' {α : Type*} [normed_linear_ordered_field α]
  [order_topology α] {p q : ℕ} (hpq : p < q) :
  is_o (λ (x : α), x^p) (λ (x : α), x^q) at_top :=
begin
  refine (is_o_iff_tendsto' _).mpr (tendsto_pow_div_pow_at_top_of_lt hpq),
  rw eventually_iff_exists_mem,
  exact ⟨set.Ioi 0, Ioi_mem_at_top 0, λ x (hx : 0 < x) hxq, (pow_ne_zero q hx.ne.symm hxq).elim⟩,
end

lemma polynomial.eval_eq_range_sum [semiring α] (P : polynomial α) (x : α) : 
  eval x P = ∑ i in range (P.nat_degree + 1), P.coeff i * x ^ i :=
begin
  rw eval_eq_sum,
  refine P.sum_of_support_subset _ _ _,
  { intros a,
    rw [mem_range, nat.lt_add_one_iff],
    exact le_nat_degree_of_mem_supp a },
  { intros,
    exact zero_mul _ }
end

lemma polynomial.eval_eq_range_sum' [semiring α] (P : polynomial α) : 
  (λ x, eval x P) = (λ x, ∑ i in range (P.nat_degree + 1), P.coeff i * x ^ i) :=
begin
  ext,
  exact P.eval_eq_range_sum x
end

lemma polynomial.eval_is_equivalent_at_top_eval_lead
  [normed_linear_ordered_field α] [order_topology α] (P : polynomial α) : 
  (λ x, eval x P) ~[at_top] (λ x, P.leading_coeff * x ^ P.nat_degree) :=
begin
  by_cases h : P = 0,
  { simp [h] },
  { conv 
    { congr,
      funext,
      rw [polynomial.eval_eq_range_sum, sum_range_succ, add_comm] },
    exact is_equivalent.refl.add_is_o (is_o.sum $ λ i hi, is_o.const_mul_left 
      (is_o.const_mul_right (λ hz, h $ leading_coeff_eq_zero.mp hz) $ 
        is_o_pow_pow_at_top_of_lt' (mem_range.mp hi)) _) }
end

noncomputable
instance : normed_linear_ordered_field ℝ :=
⟨dist_eq_norm, normed_field.norm_mul⟩

lemma polynomial.eval_div_tendsto_zero_of_degree_lt [normed_linear_ordered_field α] 
  [order_topology α] (P Q : polynomial α) (hdeg : P.degree < Q.degree) : 
  tendsto (λ x, (eval x P)/(eval x Q)) at_top (𝓝 0) :=
begin
  refine (P.eval_is_equivalent_at_top_eval_lead.symm.div 
          Q.eval_is_equivalent_at_top_eval_lead.symm).tendsto_nhds _,
  conv 
  { congr,
    funext,
    rw ← div_mul_div },
  by_cases hPQ : P = 0 ∨ Q = 0,
  { rcases hPQ with hP | hQ,
    { simp [hP, tendsto_const_nhds] },
    { simp [hQ, tendsto_const_nhds] } },
  { push_neg at hPQ,
    rw ← mul_zero _,
    rw [degree_eq_nat_degree hPQ.1, degree_eq_nat_degree hPQ.2] at hdeg,
    refine tendsto.const_mul _ (tendsto_pow_div_pow_at_top_of_lt _),
    exact_mod_cast hdeg }
end

lemma polynomial.eval_div_tendsto_leading_coeff_div_of_degree_eq [normed_linear_ordered_field α] 
  [order_topology α] (P Q : polynomial α) (hdeg : P.degree = Q.degree) : 
  tendsto (λ x, (eval x P)/(eval x Q)) at_top (𝓝 $ P.leading_coeff / Q.leading_coeff) :=
begin
  refine (P.eval_is_equivalent_at_top_eval_lead.symm.div 
          Q.eval_is_equivalent_at_top_eval_lead.symm).tendsto_nhds _,
  conv 
  { congr,
    funext,
    rw ← div_mul_div,
    rw nat_degree_eq_of_degree_eq hdeg,
    skip, skip,
    rw ← mul_one (P.leading_coeff / Q.leading_coeff) },
  exact tendsto.const_mul _ (tendsto_const_nhds.congr' $ (eventually_gt_at_top 0).mono $ 
    λ x (hx : 0 < x), (div_self (pow_pos hx Q.nat_degree).ne.symm).symm),
end

lemma polynomial.eval_div_tendsto_at_top_of_degree_gt [normed_linear_ordered_field α]
  [order_topology α] (P Q : polynomial α) (hdeg : Q.degree < P.degree) 
  (hQ : Q ≠ 0) (hnng : 0 ≤ P.leading_coeff/Q.leading_coeff) : 
  tendsto (λ x, (eval x P)/(eval x Q)) at_top at_top :=
begin
  refine (P.eval_is_equivalent_at_top_eval_lead.symm.div 
          Q.eval_is_equivalent_at_top_eval_lead.symm).tendsto_at_top _,
  conv
  { congr,
    funext,
    rw ← div_mul_div },
  have hP : P ≠ 0,
  { rw ← degree_nonneg_iff_ne_zero at ⊢ hQ, exact hQ.trans hdeg.le },
  have ratio_pos : 0 < P.leading_coeff/Q.leading_coeff :=
    lt_of_le_of_ne hnng (div_ne_zero (λ h, hP $ leading_coeff_eq_zero.mp h) 
      (λ h, hQ $ leading_coeff_eq_zero.mp h)).symm,
  rw [degree_eq_nat_degree hP, degree_eq_nat_degree hQ] at hdeg,
  norm_cast at hdeg,
  have one_le_nat_degree_sub : 1 ≤ P.nat_degree - Q.nat_degree :=
    (nat.le_sub_left_iff_add_le hdeg.le).mpr (nat.lt_iff_add_one_le.mp hdeg),
  exact tendsto_at_top_mul_left' ratio_pos ((tendsto_pow_at_top one_le_nat_degree_sub).congr' $ 
    (eventually_gt_at_top 0).mono $ λ x hx, pow_sub' x hx.ne.symm hdeg.le)
end

lemma polynomial.eval_div_tendsto_at_bot_of_degree_gt [normed_linear_ordered_field α]
  [order_topology α] (P Q : polynomial α) (hdeg : Q.degree < P.degree) 
  (hQ : Q ≠ 0) (hnng : P.leading_coeff/Q.leading_coeff ≤ 0) : 
  tendsto (λ x, (eval x P)/(eval x Q)) at_top at_bot :=
begin
  refine (P.eval_is_equivalent_at_top_eval_lead.symm.div 
          Q.eval_is_equivalent_at_top_eval_lead.symm).tendsto_at_bot _,
  conv
  { congr,
    funext,
    rw ← div_mul_div },
  have hP : P ≠ 0,
  { rw ← degree_nonneg_iff_ne_zero at ⊢ hQ, exact hQ.trans hdeg.le },
  have ratio_neg : P.leading_coeff/Q.leading_coeff < 0 :=
    lt_of_le_of_ne hnng (div_ne_zero (λ h, hP $ leading_coeff_eq_zero.mp h) 
      (λ h, hQ $ leading_coeff_eq_zero.mp h)),
  rw [degree_eq_nat_degree hP, degree_eq_nat_degree hQ] at hdeg,
  norm_cast at hdeg,
  have one_le_nat_degree_sub : 1 ≤ P.nat_degree - Q.nat_degree :=
    (nat.le_sub_left_iff_add_le hdeg.le).mpr (nat.lt_iff_add_one_le.mp hdeg),
  exact tendsto_at_bot_mul_left' ratio_neg ((tendsto_pow_at_top one_le_nat_degree_sub).congr' $ 
    (eventually_gt_at_top 0).mono $ λ x hx, pow_sub' x hx.ne.symm hdeg.le)
end

lemma polynomial.abs_eval_div_tendsto_at_top_of_degree_gt [normed_linear_ordered_field α]
  [order_topology α] (P Q : polynomial α) (hdeg : Q.degree < P.degree) 
  (hQ : Q ≠ 0) :
  tendsto (λ x, abs ((eval x P)/(eval x Q))) at_top at_top :=
begin
  by_cases h : 0 ≤ P.leading_coeff/Q.leading_coeff,
  { exact tendsto_abs_at_top_at_top.comp (P.eval_div_tendsto_at_top_of_degree_gt Q hdeg hQ h) },
  { push_neg at h, 
    exact tendsto_abs_at_bot_at_top.comp (P.eval_div_tendsto_at_bot_of_degree_gt Q hdeg hQ h.le) }
end

example : tendsto (λ x : ℝ, (3*x^2 - 6*x + 7)/(12*x^2 + 4)) at_top (𝓝 (1/4)) :=
begin
  have key1 : ∀ x:ℝ, 3*x^2-6*x+7 = eval x (monomial 2 3 - monomial 1 6 + monomial 0 7) := by simp,
  have key2 : ∀ x:ℝ, 12*x^2+4 = eval x (monomial 2 12 + monomial 0 4) := by simp,
  simp_rw [key1, key2],
  set A : polynomial ℝ := monomial 2 3 - monomial 1 6 + monomial 0 7,
  set B : polynomial ℝ := monomial 2 12 + monomial 0 4,

  have degA1 : (monomial 2 3 : polynomial ℝ).degree = (2:ℕ) := degree_monomial _ (by norm_num),
  have degA2 : (monomial 1 6 : polynomial ℝ).degree = (1:ℕ) := degree_monomial _ (by norm_num),
  have degA3 : (monomial 0 7 : polynomial ℝ).degree = (0:ℕ) := degree_monomial _ (by norm_num),
  have degA4 : (monomial 2 3 - monomial 1 6 : polynomial ℝ).degree = (2:ℕ) :=
    degA1 ▸ degree_sub_eq_left_of_degree_lt (by rw [degA1, degA2] ; dec_trivial),
  have degA : A.degree = (2:ℕ) :=
    degA4 ▸ degree_add_eq_left_of_degree_lt (by rw [degA3, degA4] ; dec_trivial),
  
  have degB1 : (monomial 2 12 : polynomial ℝ).degree = (2:ℕ) := degree_monomial _ (by norm_num),
  have degB2 : (monomial 0 4 : polynomial ℝ).degree = (0:ℕ) := degree_monomial _ (by norm_num),
  have degB : B.degree = (2:ℕ) :=
    degB1 ▸ degree_add_eq_left_of_degree_lt (by rw [degB1, degB2] ; dec_trivial),

  have leadA : A.leading_coeff = 3,
  { unfold leading_coeff nat_degree,
    rw degA,
    simp only [coeff_add,coeff_sub,coeff_monomial,if_true,option.get_or_else_coe,eq_self_iff_true],
    norm_num },

  have leadB : B.leading_coeff = 12,
  { unfold leading_coeff nat_degree,
    rw degB,
    simp only [coeff_add,coeff_sub,coeff_monomial,if_true,option.get_or_else_coe,eq_self_iff_true],
    norm_num },
  
  convert A.eval_div_tendsto_leading_coeff_div_of_degree_eq B (degA.trans degB.symm) using 2,
  rw [leadA, leadB],
  norm_num
end

/-variables [ordered_ring α]

set_option profiler true
lemma polynomial.eval_is_equivalent_at_top_eval_lead
  [normed_linear_ordered_field α] [order_topology α] (P : polynomial α) : 
  (λ x, eval x P) ~[at_top] (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) :=
begin
  rw is_equivalent,
  have : (λ x, eval x P) - (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) = 
    λ x, eval x P.erase_lead,
  { simp_rw [← self_sub_C_mul_X_pow, eval_sub], refl },
  rw [this, C_mul_X_pow_eq_monomial, is_o_iff_tendsto'], 
  { conv 
    { congr, 
      funext, 
      rw [eval_monomial, polynomial.eval_eq_range_sum, sum_div,
          sum_congr rfl (λ n hn, (div_mul_div (P.erase_lead.coeff n) 
            (P.leading_coeff) (x^n) (x^P.nat_degree)).symm)],
      skip, 
      skip,
      congr,
      rw ← sum_eq_zero (λ n (hn : n ∈ range (P.erase_lead.nat_degree + 1)), rfl) },
    refine tendsto_finset_sum _ (λ c hc, _),
    rcases P.erase_lead_nat_degree_lt_or_erase_lead_eq_zero with h | h,
    { rw ← mul_zero (P.erase_lead.coeff c / P.leading_coeff),
      refine tendsto_const_nhds.mul _,
      rw [mem_range, nat.lt_add_one_iff] at hc,
      have : c < P.nat_degree := by linarith, 
      suffices h : tendsto (λ (x : α), x ^ ((c : ℤ) - P.nat_degree)) at_top (𝓝 0),
      { refine (tendsto_congr' ((eventually_gt_at_top (0 : α)).mono (λ x hx, _))).mp h,
        simp [fpow_sub hx.ne.symm] },
      rw [← neg_sub, ← int.coe_nat_sub this.le],
      have : 1 ≤ P.nat_degree - c := nat.sub_pos_of_lt this,
      exact @tendsto_pow_neg_at_top α _ _ (by apply_instance) _ this, },
    { simp [h, tendsto_const_nhds] } },
  { sorry },
end

#check int.coe_nat_sub

lemma polynomial.eval_is_equivalent_at_top_eval_lead [normed_field α] (P : polynomial α) : 
  (λ x, eval x P) ~[at_top] (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) :=
begin
  rw is_equivalent,
  have : (λ x, eval x P) - (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) = 
    λ x, eval x P.erase_lead,
  { simp_rw [← self_sub_C_mul_X_pow, eval_sub], refl },
  rw [this, is_o_iff_exists_eq_mul, C_mul_X_pow_eq_monomial],
  use (λ x, (eval x P.erase_lead) / (P.leading_coeff * x ^ P.nat_degree)),
  split,
  { conv 
    { congr, 
      funext, 
      rw [polynomial.eval_eq_range_sum, sum_div,
          sum_congr rfl (λ n hn, (div_mul_div (P.erase_lead.coeff n) 
            (P.leading_coeff) (x^n) (x^P.nat_degree)).symm)],
      skip, 
      skip,
      congr,
      rw ← sum_eq_zero (λ n (hn : n ∈ range (P.erase_lead.nat_degree + 1)), rfl) },
    refine tendsto_finset_sum _ (λ c hc, _),
    rw ← mul_zero (P.erase_lead.coeff c / P.leading_coeff),
    refine tendsto_const_nhds.mul _,
    rw mem_range at hc,
    rw nat.lt_add_one_iff at hc,
    have := P.erase_lead_nat_degree_lt_or_erase_lead_eq_zero,
    rcases this with h | h,
    { have : c + 1 ≤ P.nat_degree := by linarith, 
      simp [div_eq_mul_inv, ← pow_sub'], sorry },
    { simp only [h, le_zero_iff_eq, nat_degree_zero] at hc,
      simp only [hc, one_div, pow_zero],
      refine tendsto_inv_at_top_zero.comp tendsto_pow_at_t, } },
  { simp,
    symmetry,
     },
end

lemma polynomial.eval_is_o_at_top_eval_of_degree_lt [normed_ring α] {P Q : polynomial α} (h : P.degree < Q.degree) :
  is_o (λ x, eval x P) (λ x, eval x Q) at_top :=
begin
  sorry
end

lemma polynomial.eval_is_equivalent_at_top_eval_lead [normed_ring α] (P : polynomial α) : 
  (λ x, eval x P) ~[at_top] (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) :=
begin
  rw is_equivalent,
  have : (λ x, eval x P) - (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) = 
    λ x, eval x P.erase_lead,
  { simp_rw [← self_sub_C_mul_X_pow, eval_sub], refl },
  rw this,
  sorry
end-/

#lint