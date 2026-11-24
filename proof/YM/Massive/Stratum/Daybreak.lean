import YM.Massive.Stratum.Taxonomy
import YM.Massive.Stratum.Receipt
import YM.Massive.Stratum.Fold
/-!
# Restoring full spin first and second (connection) jet pages

Costs (post-block-radius constants) chosen before the
large physical volume step. This version permits damage at a change of stride, then recovery
at fixed stride, including narrowing *or widening*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden.Transfer
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Birth Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior Fog
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {j k m i:ℕ} {K:KernelChoices} {E: Patch}{p:Clip}{η Ω Θ σ C B u v a b c r:ℝ}
namespace Collar
open YM.Massive.Stratum
variable (F:Plan j) (G: Plan k)
local notation "V₀"=> Back E K j k p u v
variable (N : Push.Uniform.Before su u v E.J K i)

abbrev Hat (m:ℕ)(X:Price):= Offer m X.r X.bill
section
variable (E K p u v η Ω Θ) -- endpoints

def Draw (F:Plan j)(G: Plan k)(E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ) (T Y:Price): Prop:= ∀ (V:Back E K j k p u v) (_:Avenue V η Ω Θ) (X:Hat 1 T),∃ Z:Hat 1 Y,∀ i,Tender (V.charge F G X.lamp i) (castF (Z.lamp _)) 2

def Spur (F:Plan j)(G: Plan k)(E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ) (T V':Price)(W Y:Price): Prop := ∀ (V:Back E K j k p u v) (_:Avenue V η Ω Θ) (P:Hat 1 T)(Q:Hat 1 V') (X:Hat 2 W),
    (∀ i,Tender (V.charge F G P.lamp i) (castF (Q.lamp _)) 2) → ∃ Z:Hat 2 Y,∀ i,Tender (V.charge F G (P.lamp+X.lamp) i) (castF ((Q.lamp+Z.lamp) _)) 3
end
/-- Pre-block radii for inheritance. -/
def Bend (F:Plan j)(G: Plan k)(η Ω Θ:ℝ)(m:ℕ) (P:Price): Prop:=∀ (K:KernelChoices)(E:Patch)(p:Clip)(u v:ℝ)
    (V: Back E K j k p u v) (_:Engine V η Ω Θ) (Y:On)(r s c:ℝ)(W:Offer m r c), 0 < r → 0 < s → s ≤ P.r → s*(1+m) ≤ r*E.L.val → Vital Y → (Clan V.chain (V.charge F G Y) ∧ ∀ j,Noble (V.charge F G Y j)) →(Clan V.chain (V.charge F G (Y+W.lamp)) ∧ ∀ j,Noble (V.charge F G (Y+W.lamp) j)) →
      ∃ A:Offer m s (P.bill/(E.L.val:ℝ)^(2*m-1)*c), ∀ i,Tender ((V.charge F G (Y+W.lamp)-V.charge F G Y) i) (castF (A.lamp _)) (m+1)
lemma leases (hm:0<m)(hj:4≤j)(hk:4≤k)(hu:0<η)(hv:0≤Ω)(ht:0≤Θ): ∃ P, Bend F G η Ω Θ m P:=by
  obtain ⟨σ,C,h,hC,H⟩:= pliant F G m hm hj hk hu hv ht; exact ⟨⟨σ,C,h,hC⟩,H⟩
include N
variable {P: Price}
lemma replenish (hA:Bend F G η Ω Θ 1 P)(hfit:P.bill/(E.L.val:ℝ) ≤ 1/2) (hs:4≤E.L.val): ∃ Q:Price,∀ X Y:Price, Q.Permit X Y→ Draw F G E K p u v η Ω Θ X Y:=by
  obtain ⟨δ,c,h,h',hx,H⟩:=classA (p:=p) F G N P.live
  let Q:Price:=⟨δ,c,h,hx⟩
  refine ⟨Q,fun X Y hY V L W=>?_⟩; let w (_:Unit):= V
  obtain ⟨A,ha⟩:=H V
  have he : Y.r ≤ δ:=hY.1; have hw:= (soluble F G N w (fun _=>0) (solar.zips N w) (fun _=>Vital.solozero) ())
  have hm:= (soluble F G N w (fun _=>0+W.lamp) (solar.more N (solar.zips N w) (solar.light N w (fun _=>W) X.live)) (fun _=>by rw [zero_add]; exact W.bright) ())
  have hd:Y.r*(1+(↑(1:ℕ):ℝ))≤ X.r*E.L.val:= by
    norm_num
    have ht:= X.live; have hh:(4:ℝ)≤ E.L.val:=by exact_mod_cast hs
    nlinarith only [hY.2.1,mul_le_mul_of_nonneg_left hh ht.le]
  obtain ⟨T,hp⟩:= hA K E p u v V L.toEngine 0 _ _ _ W X.live Y.live (he.trans h') hd Vital.solozero hw hm
  have hc:c+ P.bill/(E.L.val:ℝ)^(2*1-1)*X.bill ≤ Y.bill:=by
    norm_num; have hq:c+X.bill/2 ≤ Y.bill:= hY.2.2
    linarith only [mul_le_mul_of_nonneg_right hfit X.good,hq]
  refine ⟨((A.trims Y.live.le he le_rfl).sum T).trims Y.live.le le_rfl hc,fun i=>?_⟩
  have ht:Tender (V.charge F G W.lamp i - V.charge F G 0 i) (castF (T.lamp _)) 2:=by simpa only [zero_add,Pi.sub_apply,Nat.reduceAdd] using hp i
  have hv:=accum _ _ _ ht _ (ha i); rw [sub_add_cancel,add_comm (castF (T.lamp _))] at hv; rw [Offer.trims_lamp,Offer.sum_lamp,Offer.trims_lamp]; exact hv

lemma crown (hA: Bend F G η Ω Θ 2 P)(hfit:P.bill/(E.L.val:ℝ)^3≤1/2) (hs:6≤E.L.val) (X Z:Price): ∃ U:Price,∀ A B:Price, U.Permit A B → Spur F G E K p u v η Ω Θ X Z A B:=by
  let δ:= min X.r Z.r; let D:=max X.bill Z.bill
  have ht:0<δ:= lt_min X.live Z.live
  obtain ⟨r,t,h,h',hx,H⟩:= classB (p:=p) F G N P.live δ D ht
  let U:Price:= ⟨r,t,h,hx⟩
  refine ⟨U,fun A B hB V J W T X' hT=>?_⟩
  have hz:=B.live; have hp: B.r≤r:= hB.1
  let W':Offer 1 δ D:= W.trims ht.le (min_le_left ..) (le_max_left ..); let T':Offer 1 δ D:= T.trims ht.le (min_le_right ..) (le_max_right ..)
  obtain ⟨Y,hy⟩:= H V W' T' hT
  let w (_:Unit):=V
  have he:=solar.light N w (fun _=>W) X.live
  have hd:B.r*(1+(↑(2:ℕ):ℝ)) ≤ A.r*E.L.val:= by
    norm_num
    have ha:(6:ℝ)≤E.L.val:=by exact_mod_cast hs
    nlinarith only [mul_le_mul_of_nonneg_left ha A.live.le, hB.2.1]
  obtain ⟨B',hB'⟩:= hA K E p _ _ V J.toEngine W.lamp _ _ _ X' A.live hz (hp.trans h') hd W.bright (soluble F G N w (fun _=>W.lamp) he (fun _=>W.bright) ()) (soluble F G N w (fun _=>W.lamp+X'.lamp) (solar.more N he (solar.light N w (fun _=>X') A.live)) (fun _=>W.bright.add X'.bright) ())
  have hk:t+P.bill/(E.L.val:ℝ)^(2*2-1)*A.bill ≤ B.bill:=by norm_num; have hh : t+A.bill/2 ≤ B.bill:=hB.2.2; linarith only [hh,mul_le_mul_of_nonneg_right hfit A.good]
  refine ⟨((Y.trims hz.le hp le_rfl).sum B').trims hz.le le_rfl hk,fun i=>?_⟩
  have hB':= hB' i; rw [Pi.sub_apply] at hB'; have hh := accum _ _ _ hB' _ (show Tender (V.charge F G W.lamp i) (castF (T.lamp _)+castF (Y.lamp _)) 3 from hy i)
  rw [sub_add_cancel,add_comm (castF (B'.lamp _)), add_assoc] at hh; rw [Offer.trims_lamp,Offer.sum_lamp,Offer.trims_lamp]; exact hh

section
variable (E K p u v η Ω Θ)
omit N in
abbrev Festival (F:Plan j)(G: Plan k)(E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ):= Tangle (Draw F G E K p u v η Ω Θ) (Spur F G E K p u v η Ω Θ)
end
lemma basins {P Q: Price}(hP:Bend F G η Ω Θ 1 P)(hQ:Bend F G η Ω Θ 2 Q)(hfit:P.bill/(E.L.val:ℝ) ≤ 1/2)(hf:Q.bill/(E.L.val:ℝ)^3 ≤ 1/2)(hs:6≤E.L.val): Century (Festival F G E K p u v η Ω Θ):=by
    obtain ⟨a,ha⟩:= replenish (p:=p) F G N hP hfit (by omega)
    apply stitch _ _ (Price.hit a _ ha)
    · intro x y _ X; obtain ⟨b,hb⟩:=crown (p:=p) F G N hQ hf hs x y; exact ⟨_, hb _ _ (Price.step _ _)⟩
    intro x _; obtain ⟨b,hb⟩:=crown (p:=p) F G N hQ hf hs x x; exact Price.hit b _ hb
end Collar
end YM.QCD.Garden.Transfer
#print axioms YM.QCD.Garden.Transfer.Collar.basins
