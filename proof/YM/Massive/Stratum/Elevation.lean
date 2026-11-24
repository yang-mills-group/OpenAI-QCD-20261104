import YM.Massive.Stratum.Daybreak
import YM.QCD.Raft.Venus
/-!
# Entire QCD spin-page collar

Recovering the (`BirthR`) budgets and extracting certificates
usable in actual overlay presentations on mixed-ratio meshes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer Extra Iteration QCD.Smoke Work.F03 Voyage
open scoped Matrix Topology ContDiff BigOperators Classical Matrix.Norms.L2Operator
variable {E: Patch} {j k N B:ℕ}{K:KernelChoices}{p:Clip}{r D A u v Λ δ c Y w q g R a b d η Ω Θ:ℝ}{M: Before su u v E.J K N}
namespace Mist
open YM.Massive.Stratum Transfer.Collar Relation
abbrev Ledger:= (Price×Price)×Price

def Due (J:Plan j)(k:ℕ)(E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ)(X:Price×Price)(Y T:Price) (h:Price) (b:ℝ):Prop:= ∀ (V:Back E K j k p u v) (F:Avenue V η Ω Θ) (x:Hat 1 X.1) (y:Hat 2 X.2)(Z:Ornament Y.r Y.bill), ∃ (β:ℝ)(O:Ornament T.r T.bill), |β| ≤ b ∧ Skies J V (x.lamp+y.lamp) F.D' Z.page O.page β h.r h.bill

def Damp (J:Plan j)(k:ℕ)(E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ)(X _:Price×Price)(Y T:Price):Prop:=∃ (h:Price)(b:ℝ),0≤b ∧ Due J k E K p u v η Ω Θ X Y T h b

def Story (J:Plan j)(G:Plan k)(E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ):Ledger→Ledger→Prop := Tangle (Festival J G E K p u v η Ω Θ) (Damp J k E K p u v η Ω Θ)

/-- Transferring at any allowed extent, the fresh piece here
may also be narrowed on any given step. -/
lemma situation (J:Plan j)(K:KernelChoices)(he:0<η)(hΩ:0≤Ω)(hΘ:0≤Θ)(M:Before su u v E.J K N) (p: Clip) (X Z:Price×Price)
    (hi:cashRegister 2 η (psiPrice Ω Θ)/(E.L.val:ℝ)^2 ≤ 1/2)(k:ℕ) : ∃ T:Price,∀ Y V:Price,T.Permit Y V→ Damp J k E K p u v η Ω Θ X Z Y V:=by
  obtain ⟨w,q,g,R,Y,W,n,H⟩:= groves J E.L k zero_le_one
  obtain ⟨σ,D,hσ,hD,h⟩:= Segment.plasma (M:=M) (p:=p) (a:=X.1.r) (r:=X.2.r) (b:=X.1.bill) (c:=X.2.bill) X.1.live X.2.live J H
  let s:= min (σ/16) (η/2); let t:= s/2; have hs:0<s:=lt_min (by positivity) (by positivity); have hT:0<t:=div_pos hs (by norm_num)
  have hx:t<s:=by unfold t; linarith
  let A:=Pcost E D σ s; let d:= momentPrice 2 (s-t)*(Real.exp (12*s)*(cycleTax Θ s*A))
  have hA:0≤A:=auction_pos (credit_nn _ _ hD) hs; have hL:0 ≤ cycleTax Θ s:=by unfold cycleTax; have hp:=bootPOS s hΘ; positivity
  have hd:0≤d:=by unfold d; have hp:=momentPrice_pos 2 (sub_pos.mpr hx); positivity
  let P:Price:=⟨t,d,hT,hd⟩; let Q:Price:= ⟨σ/2,leafPrice E D σ,by positivity,leaf_bill hσ hD _⟩
  refine ⟨P,fun U U' hU =>⟨Q,2*A,by positivity,fun V F x y D₁=>?_⟩⟩
  let T : Segment E K p u v j k X.1.r X.1.bill X.2.r X.2.bill := ⟨V,x,y⟩
  obtain ⟨β,I,i,G,hB,hC,hE⟩:= raisons (U:=T.loadG) V J H T.vital hσ hD (h T) F.D' (A:=Θ) (a:=s) (fun i j => (F.merits i j).mono (show s ≤ η from (min_le_right ..).trans (by linarith)) le_rfl) F.home F.Sw hs (by unfold s; linarith [min_le_left (σ/16) (η/2)]) hT hx
  letI := i
  let W₀:Ornament t d:=⟨I,G,hB⟩
  have ha:U'.r≤t:=hU.1; let W':= W₀.trim ha le_rfl
  have hf:U'.r≤U.r*E.L.val:=by
    have h:(3:ℝ)≤ E.L.val:=by exact_mod_cast V.has ▸ V.fly.coarse
    nlinarith only [hU.2.1,mul_le_mul_of_nonneg_left h U.live.le,U.live]
  let L:= cashRegister 2 η (psiPrice Ω Θ)/(E.L.val:ℝ)^2*U.bill
  obtain ⟨Y',hY⟩:= stretch_loop V F D₁ he hΩ hΘ U'.live U.live (ha.trans (hx.le.trans (min_le_right ..))) hf
  have hv: d+L ≤ U'.bill:=by
    have hk : d+U.bill/2 ≤ U'.bill:= hU.2.2
    linarith only [mul_le_mul_of_nonneg_right hi U.good,hk]
  let v':= min U.r U'.r; have h':0<v' := lt_min U.live U'.live
  let mk:= (W'.graft Y').rise hv
  have hp:=coincide V F (W'.trim (δ:=v') (min_le_right ..) le_rfl) (Y'.trim (δ:=v') (min_le_right ..) le_rfl) (D₁.trim (δ:=v') (min_le_left ..) le_rfl) β h' hY (show Capes V W'.page β F.D' Q.r Q.bill T.loadG J from hE)
  exact ⟨β,mk,hC,hp⟩

/-- On a plateau (past the block size cutoff), reach steady
budgets in all classes from ANY budgets, in finitely many steps. Uniform
pre-block conditions and post-block budgets independent of volume and of
actual inherited pages. -/
theorem rays (J:Plan j)(G:Plan k)(hj:4≤j)(hk:4≤k)(he:0<η)(hΩ:0≤Ω)(hΘ : 0≤Θ) :∃ W : ℕ,∀ (E:Patch), W ≤ E.L.val →∀ (N:ℕ) (K:KernelChoices)(u v:ℝ)(_: Before su u v E.J K N)(p:Clip), Century (Story J G E K p u v η Ω Θ) :=by
  obtain ⟨x,hx⟩:= leases J G (m:=1) (by decide) hj hk he hΩ hΘ
  obtain ⟨y,hy⟩:= leases J G (m:=2) (by decide) hj hk he hΩ hΘ
  let t:= cashRegister 2 η (psiPrice Ω Θ)
  obtain ⟨T,hT⟩ := exists_nat_gt (max (max (2*x.bill) (2*y.bill)) (2*t))
  refine ⟨max 6 T,fun E hp N K u v M p=>?_⟩
  obtain ⟨hs,ht⟩:=max_le_iff.mp hp
  have hL:(↑T:ℝ) ≤ E.L.val:=by exact_mod_cast ht
  have hh:(6:ℝ)≤ E.L.val:=by exact_mod_cast hs
  let w:ℝ:= E.L.val; have hw:6 ≤ w:=hh; have hm:0<w:=by linarith
  obtain ⟨⟨h₁,h₂⟩,h₃⟩:= (and_congr_left (fun _=> max_le_iff)).mp (max_le_iff.mp (hT.le.trans hL))
  have hx':x.bill/w ≤1/2:= (div_le_iff₀ hm).mpr (by unfold w; linarith)
  have hL : w ≤ w^3:=by simpa using pow_le_pow_right₀ (le_of_lt (by linarith : 1<w)) (show 1 ≤ 3 by decide)
  have hy':y.bill/w^3 ≤1/2:= (div_le_iff₀ (pow_pos hm 3)).mpr (by unfold w at *; linarith)
  have hb:t/w^2≤1/2 := (div_le_iff₀ (pow_pos hm 2)).mpr (by unfold w; nlinarith only [h₃,hh])
  unfold Story; apply stitch _ _ (basins (p:=p) J G M hx hy hx' hy' hs)
  · intro x y _ A; obtain ⟨P,H⟩:= situation J K he hΩ hΘ M p x y hb k; exact ⟨P.later A,H _ _ (Price.step ..)⟩
  intro x _; obtain ⟨P,H⟩:= situation J K he hΩ hΘ M p x x hb k; exact Price.hit P _ H
end Mist
end YM.QCD.Fog
#print axioms YM.QCD.Fog.Mist.rays
