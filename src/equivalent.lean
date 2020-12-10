import analysis.calculus.deriv
import data.polynomial.erase_lead
import asymptotics2
import analysis.asymptotic_equivalent
import topology.algebra.ordered
import algebra.group.pi

open_locale asymptotics
open filter

namespace asymptotics

section

variables {α β : Type*} {u v w : α → β} [normed_group β] {l : filter α}

lemma is_equivalent.add_is_o (huv : u ~[l] v) (hwv : is_o w v l) : (w + u) ~[l] v :=
begin
  rw is_equivalent at *,
  convert hwv.add huv,
  ext,
  simp [add_sub],
end

lemma is_o.is_equivalent (huv : is_o (u - v) v l) : u ~[l] v := huv

lemma is_equivalent.neg (huv : u ~[l] v) : (λ x, - u x) ~[l] (λ x, - v x) :=
begin
  rw is_equivalent,
  convert huv.is_o.neg_left.neg_right,
  ext,
  simp,
end

end

section normed_linear_ordered_field

variables {α β : Type*} [normed_linear_ordered_field β] {u v : α → β} {l : filter α}

#check tendsto_neg_at_top_at_bot

lemma is_equivalent.tendsto_at_bot [order_topology β] (huv : u ~[l] v) (hu : tendsto u l at_bot) :
  tendsto v l at_bot :=
begin
  convert tendsto_neg_at_top_at_bot.comp (huv.neg.tendsto_at_top $ tendsto_neg_at_bot_at_top.comp hu),
  ext,
  simp
end

lemma is_equivalent.tendsto_at_bot_iff [order_topology β] (huv : u ~[l] v) :
  tendsto u l at_bot ↔ tendsto v l at_bot := ⟨huv.tendsto_at_bot, huv.symm.tendsto_at_bot⟩

end normed_linear_ordered_field

end asymptotics