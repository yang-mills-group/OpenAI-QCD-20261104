import YM.QCD.Garden.Shrine

/-! # Offer supply line. After-L constants may depend on fixed gauge budget,
plans. Admits arbitrary gauges/high histories under those clips.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Garden.Transfer
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Birth Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run Work.F08 Work.F03 Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {j k m i:ℕ} {K:KernelChoices} {E: Patch}{p:Clip}{η Ω Θ σ C B u v a b c r:ℝ}
variable (F:Plan j) (G: Plan k)
local notation "V₀"=> Back E K j k p u v
variable (N : Push.Uniform.Before su u v E.J K i)

include N in
lemma classA (hr:0<a): ∃ δ c, 0<δ∧δ≤a∧0≤c ∧ ∀ V:Back E K j k p u v,∃ A : Offer 1 δ c, ∀ n,Tender (V.charge F G 0 n) (castF (A.lamp _)) 2:=by
  let D:= fun i:Back E K j k p u v=>(0:On); let S:= fun i:Back E K j k p u v=>i.port
  obtain ⟨t,c,ht,hc,H⟩:= gemology (P:=fun i:Back E K j k p u v=>i.fly) (S:=fun i:Back E K j k p u v=>i.chain) S F G E (fun i=>i.origin) N (D:=D) (fun i=> Vital.solozero) (solar.zips N (fun i:Back E K j k p u v=>i))
  have hx:=lt_min hr ht
  refine ⟨_,_,hx,min_le_left ..,hc,fun V=>?_⟩
  obtain ⟨W,hW,hP,H⟩:=H V; exact ⟨⟨_,_,reduction hW hx.le (min_le_right ..) le_rfl,hP⟩,H⟩

structure Carve (E:Patch)(K:KernelChoices)(F:Plan j)(G:Plan k)(p:Clip)(u v r c:ℝ) where
 V : Back E K j k p u v
 M : Offer 1 r c
 X : Offer 1 r c
 h (i:ℕ) : Tender (V.charge F G M.lamp i) (castF (X.lamp _)) 2

include N in
lemma classB (ht:0<a) (r c:ℝ)(hr:0<r):∃ δ d, 0<δ∧δ≤a∧0≤d ∧ ∀ V:Back E K j k p u v, ∀ W T:Offer 1 r c,
    (∀ i,Tender (V.charge F G W.lamp i) (castF (T.lamp _)) 2)→∃ X : Offer 2 δ d,
    ∀ i,Tender (V.charge F G W.lamp i) (castF (T.lamp _)+castF (X.lamp _)) 3:=by
  let S:=Carve E K F G p u v r c; let D := fun i:S=> i.V; let f:= fun i:S=>i.M
  obtain ⟨t,d,h,hP,H⟩:= geology (P:=fun i:S=> i.V.fly) (S:=fun i:S=>i.V.chain) (fun i:S=>i.V.port) F G E (fun i:S=>i.V.origin) N (D:=fun i:S=> i.M.lamp) (fun i=>i.M.bright)
    (solar.light N D f hr) (fun i=>i.X.roots) (fun i=>i.X.W) hr (fun i=> i.X.price) (fun i=> i.X.bright) (fun i n=>i.h n)
  have hh:=lt_min ht h
  refine ⟨_,_,hh,min_le_left ..,hP,fun Y W T hT=>?_⟩
  let U:S:=⟨Y,W,T,hT⟩
  obtain ⟨P,hC,hW,H⟩:=H U
  let X: Offer 2 (min a t) d:= ⟨_,_,reduction hC hh.le (min_le_right ..) le_rfl,hW⟩
  refine ⟨X,fun n=>?_⟩
  have hr:Tender (Y.charge F G W.lamp n-castF (T.lamp _)) (castF (X.lamp _)) 3:=H n
  refine ⟨by rw [← sub_sub]; exact hr.1, (hT n).2.1, (hT n).2.2.add hr.2.2⟩

abbrev Assemble (P: Plan j)(T: Plan k) (η Ω Θ:ℝ)(m:ℕ)(r c:ℝ) := ∀ (K:KernelChoices)(E:Patch)(p:Clip)(u v:ℝ)
    (V: Back E K j k p u v) (_:Engine V η Ω Θ) (Y:On)(σ C:ℝ)(W:Offer m σ C), 0 < σ → σ ≤ r → (1+m) ≤ E.L.val → Vital Y → (Clan V.chain (V.charge P T Y) ∧ ∀ j,Noble (V.charge P T Y j)) →(Clan V.chain (V.charge P T (Y+W.lamp)) ∧ ∀ j,Noble (V.charge P T (Y+W.lamp) j)) →
      ∃ A:Offer m σ (c/(E.L.val:ℝ)^(2*m-1)*C), ∀ i,Tender ((V.charge P T (Y+W.lamp)-V.charge P T Y) i) (castF (A.lamp _)) (m+1)

include N in
lemma including (hA: Assemble F G η Ω Θ 1 σ C)(ht:0<σ)(hC:0≤C)(hfit:C/(E.L.val:ℝ) ≤ 1/2)(hs:3≤E.L.val): ∃ δ c,0<δ∧0 ≤ c ∧ ∀ V:Back E K j k p u v,∀ W:Offer 1 δ c,∀ _ : Engine V η Ω Θ,
    ∃ A:Offer 1 δ c,∀ i,Tender (V.charge F G W.lamp i) (castF (A.lamp _)) 2 := by
  obtain ⟨δ,c,h,h',hx,H⟩:=classA F G N ht
  refine ⟨δ,2*c,h,by positivity,fun V W J=>?_⟩
  let v (_:Unit):=V
  obtain ⟨A,ha⟩:=H V
  obtain ⟨B,hp⟩:= hA K E p _ _ V J 0 _ _ W h h' (by omega) Vital.solozero (soluble F G N v (fun _=>0) (solar.zips N v) (fun _=>Vital.solozero) ()) (soluble F G N v (fun _=>0+W.lamp) (solar.more N (solar.zips N v) (solar.light N v (fun _=>W) h)) (fun _=>by rw [zero_add]; exact W.bright) ())
  have hc:c+C/(E.L.val:ℝ)^(2*1-1)*(2*c)≤2*c:=by norm_num at *; nlinarith
  refine ⟨(A.sum B).trims h.le le_rfl hc,fun i=>?_⟩
  have hp:Tender (V.charge F G W.lamp i-V.charge F G 0 i) (castF (B.lamp _)) 2:= by simpa only [zero_add,Pi.sub_apply,Nat.reduceAdd] using hp i
  have hv:=accum _ _ _ hp _ (ha i); rw [sub_add_cancel,add_comm (castF (B.lamp _))] at hv; rw [Offer.trims_lamp,Offer.sum_lamp]; exact hv

include N in
lemma exit_plate (δ c:ℝ)(hp:0<δ)(hA: Assemble F G η Ω Θ 2 σ C)(ht:0<σ)(hC:0≤C)(hfit:C/(E.L.val:ℝ)^3≤1/2)(hs:3≤E.L.val): ∃ r d,0<r∧0≤d ∧ ∀ (V: Back E K j k p u v) (W T: Offer 1 δ c),∀ X:Offer 2 r d,∀ _:Engine V η Ω Θ,
    (∀ i,Tender (V.charge F G W.lamp i) (castF (T.lamp _)) 2) →
    ∃ A:Offer 2 r d,∀ i,Tender (V.charge F G (W.lamp+X.lamp) i) (castF ((T.lamp+A.lamp) _)) 3:=by
  obtain ⟨r,t,h,h',hx,H⟩:=classB F G N ht δ c hp
  refine ⟨r,2*t,h,by positivity,fun V W T X J hT=>?_⟩
  obtain ⟨A,ha⟩:= H V W T hT
  let v(_:Unit):= V
  have he:=solar.light N v (fun _=>W) hp
  obtain ⟨B,hB⟩:= hA K E p u _ V J W.lamp r _ X h h' (by omega) W.bright (soluble F G N v (fun _=>W.lamp) he (fun _=>W.bright) ()) (soluble F G N v (fun _=>W.lamp+X.lamp) (solar.more N he (solar.light N v (fun _=>X) h)) (fun _=> W.bright.add X.bright) ())
  have hc : t+C/(E.L.val:ℝ)^(2*2-1)*(2*t)≤2*t:=by norm_num; nlinarith
  refine ⟨(A.sum B).trims h.le le_rfl hc,fun i=>?_⟩
  have hB:= hB i; rw [Pi.sub_apply] at hB; have hh := accum _ _ _ hB _ (ha i)
  rw [sub_add_cancel,add_comm (castF (B.lamp _)), add_assoc] at hh; rw [Offer.trims_lamp,Offer.sum_lamp]; exact hh

def Bears (F:Plan j)(G:Plan k)(E:Patch)(K:KernelChoices)(η Ω Θ u v:ℝ)(p:Clip):Prop:= ∃ δ c r d:ℝ, 0 < δ ∧ 0 < r ∧ 0≤c∧0≤d ∧ ∀ (V:Back E K j k p u v) (W: Offer 1 δ c) (T:Offer 2 r d), Engine V η Ω Θ→∃ (A:Offer 1 δ c) (B:Offer 2 r d),∀ i, Tender (V.charge F G W.lamp i) (castF (A.lamp _)) 2 ∧ Tender (V.charge F G (W.lamp+T.lamp) i) (castF ((A.lamp+B.lamp) _)) 3
lemma harvestH (hj:4≤j)(hk:4≤k)(he:0<η)(hp:0≤Ω)(ht:0≤Θ):∃ L:ℕ,∀ (E: Patch), L≤E.L.val →∀ (K:KernelChoices)(p:Clip)(u v:ℝ)(i:ℕ), (Push.Uniform.Before su u v E.J K i) → Bears F G E K η Ω Θ u v p:=by
  obtain ⟨σ,C,h,hC,H⟩:= kind F G 1 zero_lt_one hj hk he hp ht
  obtain ⟨ρ,c,h',hc,H'⟩:= kind F G 2 (by omega) hj hk he hp ht
  obtain ⟨L,hL⟩:= exists_nat_gt (2*C+2*c); refine ⟨max 3 L,fun E hv K p u v i N=>?_⟩
  obtain ⟨hS,hv⟩:=max_le_iff.mp hv; let w:ℝ:= E.L.val; have ht : (↑L:ℝ)≤w:=by unfold w; exact_mod_cast hv
  have hw : 3≤w:=by unfold w; exact_mod_cast hS
  have ha: 0<w:=by linarith
  have hF : C/w≤1/2:= (div_le_iff₀ ha).2 (by linarith)
  have hh:w≤w^3:=by simpa using pow_le_pow_right₀ (le_of_lt (by linarith : 1<w)) (show 1 ≤ 3 by decide)
  obtain ⟨r,C1,hx,hx',W⟩:= including F G N H h hC hF hS
  obtain ⟨s,C2,hi,hi',S⟩:= exit_plate F G N r C1 hx H' h' hc ((div_le_iff₀ (pow_pos ha 3)).2 (by linarith : c≤1/2*w^3)) hS
  refine ⟨_,_,_,_,hx,hi,hx',hi',fun V A Y J=>?_⟩
  obtain ⟨B,hB⟩:= W V A J; obtain ⟨D,hD⟩:= S V A B Y J hB; exact ⟨_,_,fun i=>⟨hB i,hD i⟩⟩
end YM.QCD.Garden.Transfer
