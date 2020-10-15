import analysis.calculus.deriv
import algebra.group.pi

namespace asymptotics

open filter

open_locale topological_space

section normed_group

variables {α β : Type*} [normed_group β] 

def is_equivalent (u v : α → β) (l : filter α) := is_o (u - v) v l

notation u ` ~[`:50 l:50 `] `:0 v:50 := is_equivalent u v l

variables {u v w : α → β} {l : filter α}

lemma is_equivalent.is_o (h : u ~[l] v) : is_o (u - v) v l := h

lemma is_equivalent.is_O (h : u ~[l] v) : is_O u v l :=
(is_O.congr_of_sub h.is_O.symm).mp (is_O_refl _ _)

lemma is_equivalent.is_O_symm (h : u ~[l] v) : is_O v u l :=
begin
  convert h.is_o.right_is_O_add,
  ext,
  simp
end

lemma is_equivalent.refl : u ~[l] u :=
begin
  rw [is_equivalent, sub_self],
  exact is_o_zero _ _
end

lemma is_equivalent.symm (h : u ~[l] v) : v ~[l] u :=
(h.is_o.trans_is_O h.is_O_symm).symm

lemma is_equivalent.trans (huv : u ~[l] v) (hvw : v ~[l] w) : u ~[l] w :=
begin
  rw is_equivalent,
  convert (huv.is_o.trans_is_O hvw.is_O).add hvw.is_o,
  ext,
  repeat {rw pi.sub_apply},
  abel
end

lemma is_equivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0 :=
begin
  rw [is_equivalent, sub_zero],
  exact is_o_zero_right_iff
end

lemma is_equivalent_const_iff_tendsto {c : β} (h : c ≠ 0) : u ~[l] (λ _, c) ↔ tendsto u l (𝓝 c) :=
begin
  rw [is_equivalent, is_o_const_iff h],
  split; intro h;
  [ { have := h.add tendsto_const_nhds, rw zero_add at this }, 
    { have := h.add tendsto_const_nhds, rw ← sub_self c} ];
  convert this; ext; simp [sub_eq_add_neg]
end

lemma is_equivalent.tendsto {c : β} (hu : u ~[l] (λ _, c)) : filter.tendsto u l (𝓝 c) :=
begin
  rcases (em $ c = 0) with ⟨rfl, h⟩,
  { exact (tendsto_congr' $ is_equivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds },
  { exact (is_equivalent_const_iff_tendsto h).mp hu }
end

end normed_group

section normed_field

variables {α β : Type*} [normed_field β] {u v w : α → β} {l : filter α}

lemma is_equivalent_iff_exists

end normed_field

end asymptotics

#lint