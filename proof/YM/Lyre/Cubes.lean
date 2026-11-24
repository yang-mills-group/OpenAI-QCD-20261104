import YM.Lyre.Dull
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Quills.Eden
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter Stitch Stitch.Tablet
open MassiveQCD.Ribbon MassiveQCD.Play MassiveQCD.Play.Chamber Apron Cupola
open QCD.Lat Lattice Cape LampV
open scoped Topology ContDiff BigOperators Classical TensorProduct Matrix.Norms.L2Operator
open YM.Arise.Bill YM.Arise.Count
variable {c:Side}{n N:ℕ}{A B I J:Type}[Fintype A][Fintype B][Fintype I][Fintype J]
local notation "K" => Keys c N
variable (Q:I→Bool)(p: Finset I) (t: Patio (Spine I))
lemma pigment (Y:Support c): clad (limits (F:=N) Y) ((qraft (Keys c N) (Spine I) t).val):=by
    let x:=t.val; have hx:=clad.attend (1:Alg K) x (Subalgebra.one_mem (region (limits (F:=N) Y))); rw[map_one,one_mul] at hx; exact hx
lemma paintTint (k:Frame c): parcelColor N k I (qraft (Keys c N) (Spine I) t) = qraft (Keys c N) (Spine I) t:=by
    apply Subtype.ext; let K':=(slots N k).toLinearMap.toContinuousLinearMap; let X:= t.val
    change carry _ K' (quill _ X)=quill _ X
    have hx:=carries_r K' (1: Alg ((Keys c N) ⊕ Spine I)) X; rw [one_mul,show carry (Spine I) K' 1=1 from ?_,one_mul] at hx; exact hx
    let P:=fiber (Spine I) (A:=Keys c N); let u:Alg (Keys c N):=1; have hp:stake (Keys c N) (∅:Finset (Spine I)) u=P u:=quiet ..; rw [← show P u=1 from map_one P,← hp,speaks,show K' u=u from map_one (slots N k)]
lemma numberT (v:Alg A)(P: Patio (Spine I)) (s: Finset (Spine I)): scrape A s (fiber (Spine I) v* (qraft A (Spine I) P).val)= coef s P.val • v := plucks ..
lemma coatC (hp:Honest Q p t): t.val = coef (burst Q p) t.val • mono (burst Q p):=by
    let A:=Unit; have hp : Polite Q p ((qraft A (Spine I)) t):= hp Unit; have h(t' : Finset (Spine I)) : scrape A t' ((qraft A (Spine I) t).val) = coef t' t.val • 1 :=by
        have h:=numberT (1:Alg A) t t'; rwa [map_one,one_mul] at h
    nth_rw 1 [← write t.val]; rw [sum_eq_single (burst Q p)]
    · intro i hi hx; have he:= hp.spectral _ hx; rw [h] at he; rw [(smul_eq_zero.mp he).resolve_right (one_ne_zero (α:=Alg Unit)),zero_smul]
    simp
-- bound to authorize receipts
lemma packs (v:Finset I): (burst Q v).card ≤ v.card*6:=by
    induction v using Finset.induction_on with | empty=> simp|insert a v hv ih=> rw [←singleton_union,pulver Q]; apply (card_union_le ..).trans; have hh :(burst Q {a}).card≤ 6:=by rw[onePost]; split_ifs <;> omega
                                                                                 rw [singleton_union,card_insert_of_notMem hv]; omega
lemma pines (hp: Honest Q p t)(hm:6 ≤n): (qraft A (Spine I) t).val ∈ QCD.Anomaly.Rim univ (p.card*n):=by
    change quill _ t.val ∈ _; rw [coatC Q p t hp,map_smul]; apply Submodule.smul_mem; let a:=Embedding.inr (α:=A) (β:=Spine I); let b:=(burst Q p).map a
    have h:b.card≤ p.card*n:= by rw[show b.card= _ from card_map a]; exact (packs Q p).trans (Nat.mul_le_mul_left _ hm)
    have hv:mono b ∈ QCD.Anomaly.Rim univ (p.card*n):= QCD.Anomaly.Rim.layerIn (subset_univ _) h
    rcases embed_blade a (burst Q p) with H|H <;> change embed a _∈ _ <;> rw [H]; exact hv; exact Submodule.neg_mem _ hv
lemma coverX (o:I→Site c)(v:ℝ)(hp: Honest Q p t)(hm:6 ≤ n)(ht:1 ≤ v)(C:ℝ)(h: ‖qraft (Keys c N) _ t‖≤C): let W:=qraft (Keys c N) _ t; (∀ X: Support c, Stitch.lights p X o Q W) ∧ (∀ k: Frame c, parcelColor N k I W=W) ∧ W.val∈ QCD.Anomaly.Rim univ (p.card*n) ∧ Stitch.Tablet.credits v W≤ v^(p.card*n)*C:= by
    intro W; have he : W.val∈ QCD.Anomaly.Rim univ (p.card*n):=pines Q p t hp hm
    exact ⟨fun V=>⟨hp _,pigment t V⟩, fun k=> paintTint t k,he,(warmP N _ W he ht).trans (mul_le_mul_of_nonneg_left h (pow_nonneg (zero_le_one.trans ht) _))⟩
end YM.MassiveQCD.Sample.Quills.Eden
#print axioms YM.MassiveQCD.Sample.Quills.Eden.coverX
