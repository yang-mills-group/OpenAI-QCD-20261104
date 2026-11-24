import YM.Pods.Axes
import YM.Massive.Target.Euclidean
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry Chess.Fortuna
variable (S:Scheme){C:Sequence} {d:ℕ}
variable (Yv:ℝ) (Ht:SourceRead.TaperHol){Go:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Go)(sym:RawSym)(base:ℕ→ℕ) (U:Massive.Lining.Temper.Collage.Exhibit.CoreMix)
local notation "cK"=>C.S
local notation "ς" j:arg=>C.S.side (C.R j)
local notation "γ"=>clock cK
local notation "Pκ" => Uv.display C Ht sym U base
local notation "Ψ"=> Bloom Uv
variable (w:Label d)(q:Bool)(hp: moored w.val q)(hw:w ≠0)
-- bounds same fixed reference across all ≤24 rotations, convert budgets.All.Point.R.One.G minimal interior.fit. Y.Opacity.S
variable (hX:(Uv.display C Ht sym U base).System)
variable (hY:Spent C (Uv.display C Ht sym U base))
variable (e:ℝ)(he:0<e)
variable (hs:Sway C.S){β ν:ℝ}(hC:C.Path β ν)
local notation "V₁"=> rayM C.S d e
set_option quotPrecheck false
local notation "Ω" i:arg => (C.A i).regulator
variable {n:ℕ}(D: Fin n→ℕ)(u:(i:Fin n)→ Label (D i))(s: Fin n→ Bool)
abbrev seaM(C:Sequence)(i j:ℕ) (f:Fin n→ Cover):= Romance.Clear (ratioTo C.S (C.N i) j) (wrap (C.S.side (C.R i) (C.N i)) ∘ f) -- strict numeric
noncomputable def pricedh (j:ℕ)(a:ℝ):= a*∏ i:Fin n, Hub.rayM S (D i) e 1 j
noncomputable def metricP (C:Sequence)(P:Calibration C)(d:Fin n→ℕ)(u:(i:Fin n)→Label (d i)) (i:ℕ)(f:Fin n→ Cover):= (C.A i).regulator.average (List.ofFn (fun b=> P.physical none i (u b) (f b))).prod
abbrev watchH (C:Sequence)(P:Calibration C) (d:Fin n→ℕ)(u:(i:Fin n)→Label (d i)) (j i:ℕ)(B:ℝ):Prop:=∀ x:Fin n→ Cover, seaM C i j x→ ‖metricP C P d u i x‖ ≤ B
local notation "η"=> metricP C Pκ D
local notation "Υ"=> pricedh C.S e D
local notation "Φ"=> watchH C Pκ D
-- consistent multiplication heights all arities. Signal Big.Gain selection clock. Margin guards.Proof.Vehicle for other uses.
lemma cost_nn (j:ℕ)(d:Fin n→ℕ)(u:ℝ)(he:0 ≤u)(e:ℝ): 0 ≤ pricedh C.S e d j u:= mul_nonneg he (prod_nonneg (fun i _=> mul_nonneg zero_le_one (Real.exp_nonneg _))) -- S implicit C isn't inferred. maybe better S.
lemma invests (v:Fin n→ℝ)(j:ℕ): (∏ a:Fin n, Hub.rayM C.S (D a) e (v a) j)=pricedh C.S e D j (∏ a,v a):=by unfold pricedh Hub.rayM; simp only [one_mul, Finset.prod_mul_distrib]
include he hs hX hY hC
lemma pointPass (h:∀ i,moored (u i).val (s i)): ∃ c:ℝ,0 ≤ c∧∀ᶠ j in atTop,∀ᶠ i in atTop,watchH C (Uv.display C Ht sym U base) D u j i (Υ j c):=by
    by_cases hW:∀ i,u i≠0
    swap
    · push_neg at hW; obtain ⟨q,hq⟩:=hW; refine ⟨0,le_rfl, Filter.Eventually.of_forall (fun j=>Filter.Eventually.of_forall fun i x hx=>?_)⟩
      unfold metricP; let f(b:Fin n):= (Pκ).physical none i (u b) (x b); change ‖(Ω i).average (List.ofFn f).prod‖ ≤ _; have hf:f q=0:=by unfold f Calibration.physical; rw [hq,map_zero,map_zero]
      rw [List.prod_eq_zero (List.mem_ofFn.mpr ⟨_,hf⟩),map_zero,norm_zero]; exact cost_nn _ _ _ le_rfl _
    choose c hc hP using fun k=> starlight Ht Uv sym base U (u k) (s k) (h k) (hW k) hX hY e he hs hC -- sig
    refine ⟨∏ k,c k, Finset.prod_nonneg fun k _=> hc k, ?_⟩; filter_upwards [eventually_all.mpr hP,hs.high.eventually (eventually_gt_atTop (6*n))] with j hj hg; filter_upwards [eventually_all.mpr hj,hC.uv.tendsto_atTop.eventually_ge_atTop (j+1)] with i hi hk f hF
    let S:= cK; let P:= Pκ; let W:= Ω i; let K:= (C.S).side (C.R i) (C.N i)
    let g:=viewW cK (C.R i) hk; let g':=viewW cK (C.R i) (show j ≤ C.N i from Nat.le_of_lt hk); -- hk.le is j+1≤.. Less? h filter_ge_atTop returns j+1 ≤ C.N i, .le gives? `.le` parser with (<)`? Prop subtype.V fix.
    let t:=mural g' (evenW _ _ (hC.even i) _) (0:Site K); let F:=wrap K ∘ f
    have hPos:t.side.val= (ratioTo cK (C.N i) j):=rfl; let L:=Ratio.count g; let M:=6*n
    have hγ: n*(2*(3*L.val))<t.side.val:=by rw [hPos,step_factor hk, show n*(2*(3*L.val))= (6*n)*L.val by ring]; exact Nat.mul_lt_mul_of_pos_right hg L.pos
    obtain ⟨x,hx⟩:= t.fits_together F (3*L.val) (by positivity) hγ; let X:= t.newly x; let Y(k:Fin n):= X.which (F k); have hZ : Injective Y:= by
         intro i j he; by_contra ho; apply (not_le.mpr (hF i j ho)); let P':= (hx i).1; exact X.extent P' (show F j∈ X.chamber (Y i) from he.symm ▸ (show F j∈ X.chamber (Y j) from (hx j).1))
    let G(a:Fin n):= P.physical none i (u a) (f a); let Q(a:Fin n):= floorL X W.average W (G a) (Y a); let L₀(k:Fin n):= Hub.rayM cK (D k) e (c k) j; have hm(k:Fin n):= hi k hk X hPos rfl (Y k) (f k) (hx k); let P₁:= List.ofFn G; have hr:W.t=0:=rfl
    have hh: ‖W.average ((List.finRange n).map G).prod‖ ≤ ∏ i:Fin n,Q i:= plant X W.average W rfl G Y hZ 0 _ (List.nodup_finRange n) (fun i=>List.mem_finRange i) (fun i=>(hm i).1) hr (averageSeal X W rfl (hC.normalized i|>.beta_pos (Nat.le_refl _) |>.le) (sideW hC i _) 0) (battery hC i)
    change ‖W.average (List.ofFn G).prod‖ ≤ _; rw [List.ofFn_eq_map]; exact hh.trans ((prod_le_prod (fun i _=>floor_nn X W.average W ..) (fun i _=>(hm i).2)).trans_eq (invests ..)) -- adjust
omit he hs hX hY hC
end YM.Massive.Patria.Hub
#print axioms YM.Massive.Patria.Hub.pointPass
