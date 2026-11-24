import YM.Vest.Loom
/-! deterministic polynomial final excursion budget at REAL full even in presence of distant marks; sublevel all logs.
 estimates here do not use support for cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.Vest
open Function
open scoped BigOperators ContDiff Classical
open QCD QCD.Creek QCD.Bera QCD.Anomaly QCD.Grass QCD.Cove Finset Next.Rank Next.Rank.Normal
open MassiveQCD.Play MassiveQCD.Play.Chamber MassiveQCD.FlareV
variable {A B C D U V X Y Z I:Type}[Fintype A][Fintype B][Fintype C][Fintype D][Fintype U][Fintype V][Fintype X][Fintype Y][Fintype Z][Fintype I]
variable {n m l k:ℕ}{s t y e:ℝ}
namespace Tuck
local notation "V₀"=> Papers A (Patio X)
local notation "V₁"=> Papers B (Patio Y)
variable (T S:Tone A X B Y)
variable (f: Finset I→ Papers A (Patio X))(w:I→ℝ) {Z':Finset I}
-- export.S V support unions for ONE crest.Deters
variable {a: I→Finset A}{b: I→Finset X}
variable (hx:∀ i⊆ Z',i.Nonempty→ f i∈ Ledger (i.biUnion b) (i.biUnion a) (i.card*k) (i.card*m) ) (hp: T.Rich s) (hv:S.Rich s) (hF:T.Gale S t)
local notation "Dv"=> emmet s s s s (l*k) (l*m)
local notation "Wt"=> windfall s s s s (l*k) (l*m)
set_option quotPrecheck false
local notation "Lv" T:arg=> switch f (T).P (T).Q (T).M (T).V
local notation "gv"=> y * (Dv*age l*moneyN l)
lemma t_pane (h:1 ≤ s): 0 ≤ windfall s s s s n m:=by
    have he:0<s:=zero_lt_one.trans_le h; unfold windfall vibe shiver Anomaly.percent dime tumbler steely tumbler; positivity
lemma em_pos (h:1 ≤ s): 1 ≤ emmet s s s s n m:=MassiveQCD.Rebus.em_pos h
noncomputable def cpalm (s y:ℝ)(l k m:ℕ):= y*(emmet s s s s (l*k) (l*m)*age l *moneyN l)
noncomputable def caulk (s t y:ℝ)(l k m:ℕ):= ((face l (cpalm s y l k m^l)+1)^l)*(windfall s s s s (l*k) (l*m)*t*(age l*y^l))
lemma palmV (Z: Finset B)(W:Finset Y)(ha: Tone.Rich S s) : Sky S.P S.Q S.M S.V univ univ s s s s:=ha
include hp hx
variable (hh:Z'.card ≤ l)(hy:1 ≤y)(he:∀ j⊆ Z',j.Nonempty → cents (f j) ≤ y^j.card) (ht:0≤ t)
include hh hy he
lemma veks (i:Finset I)(hi:i⊆ Z') : cents ((Lv T) i) ≤ (cpalm s y l k m)^i.card:=by
     have hc : i.card ≤ l:= (card_le_card hi).trans hh
     have hz j (hp:j ⊆ i)(hy:j.Nonempty) := hx j (hp.trans hi) hy
     exact MassiveQCD.Play.Chamber.growth f _ _ _ _ _ _ hz y Dv hy (fun j h hh=> he j (h.trans hi) hh) hc (em_pos hp.craze) (fun x h=> tolled _ _ _ _ x (leaguer h (subset_univ _) (subset_univ _) le_rfl le_rfl) hp)
include hv hF ht
lemma columnP (i:Finset I) (hi:i⊆ Z'): cents ((Lv T) i - (Lv S) i) ≤ caulk s t y l k m:=by
     let a1:= age l * y ^ l; let v:=cpalm s y l k m^l; let u:= Wt*t*a1
     have hs : 1 ≤ cpalm s y l k m:= one_le_mul_of_one_le_of_one_le hy (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (em_pos hp.craze) (one_le_pow₀ (by norm_num))) (MassiveQCD.Rebus.sageMoney l)); have h1:0 ≤ Wt:= t_pane hp.craze; have h2:= zero_le_one.trans hy; have h3:0 ≤ u:=by unfold u a1 age; positivity
     have hJ j (hp:j⊆ i):j.card ≤ l:=(card_le_card (hp.trans hi)).trans hh
     apply spentX (s:=u) (probate B) (fun j=>T.read (parties f j)) (fun j=>S.read (parties f j)) _ ((card_le_card hi).trans hh) (one_le_pow₀ hs) h3 (fun j h hz=> (veks T f hx hp hh hy he j (h.trans hi)).trans (pow_le_pow_right₀ hs (hJ _ h))) (fun j h hz=> (veks S f hx hv hh hy he j (h.trans hi)).trans (pow_le_pow_right₀ hs (hJ _ h)))
     intro p hD hz
     have hx':= lowMark f a b (hD.trans hi) hx
     have hG:= money_fast f (probate A) y (fun j hj => he j ((mem_powerset.mp hj).trans (hD.trans hi))) hy (hJ _ hD)
     exact (momentQ _ _ _ _ _ _ _ _ _ (leaguer hx' (subset_univ _) (subset_univ _) (Nat.mul_le_mul_right _ (hJ _ hD)) (Nat.mul_le_mul_right _ (hJ _ hD))) hp hv ht hF).trans (mul_le_mul_of_nonneg_left (hG.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy (hJ _ hD)) (by unfold age; positivity))) (by positivity))
-- gauge coherent.EM input maybe shift raw→jet only before evaluate.Use FULL stencil.Log surgeries later.Item.M.El. Cost tangent allowed.
omit hp hx hh hy he hv hF ht
include hx
lemma bloomQ (i:Finset I)(hi:i⊆ Z') (he:i.Nonempty) : Tuck.tilt T w f i ∈ Ledger univ univ (i.card*k) (i.card*m):=by
     refine Submodule.smul_mem _ _ (leaguer (MassiveQCD.Play.Chamber.move f a b T.P T.Q T.M T.V (fun s hs=>hx s (hs.trans hi)) (fun _=>univ) (fun _=>univ) (fun _ _ _ _ i _=> mem_univ i) (fun _ _ _ _ i _=>mem_univ i)) (subset_univ _) (subset_univ _) le_rfl le_rfl)
end Tuck
end YM.Vest
#print axioms YM.Vest.Tuck.columnP
