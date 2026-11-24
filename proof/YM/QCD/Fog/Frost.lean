import YM.QCD.Fog.Vault

/-! # Feasible loop price at widths fixed across all sufficiently deep actual histories (given uniform gauge budgets).

None of the cost receipts claims the α matches the required sign in ONE step.
That question needs a different comparison and price lemma.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fog
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Orbit Run Revolve Flume Sparks Quarry Tavern Birth YM.Further.PhysicalPeriodLimitF933 Jacobi Macrame Push.Uniform Garden Transfer Extra Iteration QCD.Smoke Work.F03 Voyage
open scoped Matrix Topology ContDiff BigOperators Classical Matrix.Norms.L2Operator
variable {E: Patch} {j k N B:ℕ}{K:KernelChoices}{p:Clip}{r D A u v Λ δ c Y w q g R a b d η Ω Θ:ℝ}{M: Before su u v E.J K N}
def Crop (E:Patch) (K:KernelChoices) (p:Clip)(u v:ℝ)(J:Plan j)(k:ℕ)(a b r c η Ω Θ:ℝ):Prop:= ∃ σ C D R W:ℝ,0 < σ ∧ σ≤ η/2 ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 < R ∧ 0 ≤ W ∧ ∀ T:Segment E K p u v j k a b r c,∀ F: Avenue T.V η Ω Θ,∀ X: Ornament σ C,∃ (β:ℝ)(O:Ornament σ C), |β| ≤ D ∧ Skies J T.V T.loadG F.D' X.page O.page β R W

lemma afterL (hr:0<a)(ht:0<r)(J:Plan j)(K:KernelChoices)(he:0<η)(hΘ:0≤Θ)(M:Before su u v E.J K N) (p: Clip)(b c:ℝ)
    (hi:cashRegister 2 η (psiPrice Ω Θ)/(E.L.val:ℝ)^2 ≤ 1/2)(k:ℕ) : Crop E K p u v J k a b r c η Ω Θ:=by
  obtain ⟨w,q,g,R,Y,X,n,H⟩:= groves J E.L k zero_le_one
  obtain ⟨σ,D,hσ,hD,h⟩:= Segment.plasma (M:=M) (p:=p) (a:=a) (r:=r) (b:=b) (c:=c) hr ht J H
  let s:= min (σ/16) (η/2); let t:= s/2; have hs:0<s:=lt_min (by positivity) (by positivity); have hT:0<t:=div_pos hs (by norm_num)
  have hx:t<s:=by unfold t; linarith
  let A:=Pcost E D σ s; let d:= momentPrice 2 (s-t)*(Real.exp (12*s)*(cycleTax Θ s*A))
  have hA:0≤A:=auction_pos (credit_nn _ _ hD) hs; have hL:0 ≤ cycleTax Θ s:=by unfold cycleTax; have hp:=bootPOS s hΘ; positivity
  have hd:0≤d:=by unfold d; have hp:=momentPrice_pos 2 (sub_pos.mpr hx); positivity
  unfold Crop; refine ⟨t,2*d,2*A,σ/2,leafPrice E D σ,hT,hx.le.trans (min_le_right ..),by positivity,by positivity,by positivity,leaf_bill hσ hD _,fun T F X=>?_⟩
  obtain ⟨β,I,i,U,hB,hC,hE⟩:= raisons (U:=T.loadG) T.V J H T.vital hσ hD (h T) F.D' (A:=Θ) (a:=s) (fun i j => (F.merits i j).mono (show s ≤ η from (min_le_right ..).trans (by linarith)) le_rfl) F.home F.Sw hs (by unfold s; linarith [min_le_left (σ/16) (η/2)]) hT hx -- signature
  obtain ⟨W,hW⟩:= inheritG T.V F X he hT (hx.le.trans (min_le_right ..))
  letI := i
  let Z:Ornament t d:=⟨I,U,hB⟩
  have hp:=coincide T.V F Z W X β hT hW hE
  exact ⟨β,(Z.graft W).rise (by nlinarith),hC,hp⟩
lemma crops (hr: 0 < η) (hΩ:0≤Ω)(hΘ : 0≤Θ) :∃ W : ℕ,∀ (E:Patch), W ≤ E.L.val →∀ (a b r c:ℝ), 0<a→ 0 < r →∀ (j k N:ℕ) (J:Plan j)(K:KernelChoices)(u v:ℝ)(M:Before su u v E.J K N)(p:Clip), Crop E K p u v J k a b r c η Ω Θ:=by
  let d:= cashRegister 2 η (psiPrice Ω Θ)
  obtain ⟨W,h⟩ := exists_nat_gt (2*d)
  refine ⟨W,fun E hp a b r c ha ht j k N J K u v M p=> afterL ha ht J K hr hΘ M p b c ?_ k⟩
  have hm : 1 ≤ (E.L.val:ℝ):=by exact_mod_cast E.L.property
  apply (div_le_iff₀ (by positivity)).2; have hh: (↑W:ℝ)≤ E.L.val:=by exact_mod_cast hp
  change d ≤ _; nlinarith
end YM.QCD.Fog
