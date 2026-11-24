import YM.Infer.Milan
import YM.Pods.Atlases
import YM.Infer.Crest
import YM.Elms.Corner
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
local notation "ℓθ"=> 24
-- public rank apertures. some eventually maturity and y.W.Data
noncomputable abbrev deficit (d:ℕ):= Module.finrank ℂ (LinearMap.ker (@UV.Free.projection d))
variable (Q:Calibration C)
-- semantic.rank tools only. genuine lease reference.C point. lens closes forecasts, not asserting relation with bare stencils.Kern
structure Invest (Q:Calibration C)(d:ℕ) where
    bonds : ℕ→Fin (deficit d)→Label d
    scale : ℕ→ℝ
    bud : Fin (deficit d) → ℕ→ℕ→ℝ
    pos : ∀ i,0 ≤ scale i
    heights : ∀ᶠ i in atTop,∀ q: Fin (deficit d)→ℂ, ‖∑ j,q j • bonds i j‖ ≤ 1→ ‖q‖ ≤ scale i
    uniqueI : ∀ᶠ i in atTop,LinearIndependent ℂ (bonds i)
    race (k:Fin (deficit d)) : ∀ᶠ j in atTop,Tendsto (fun i=> scale i* bud k j i) atTop (𝓝 0)∧ ∀ᶠ i in atTop,wider C Q (bonds i k) (bud k j i) j i∧ 0 ≤ bud k j i
open Massive.Elm.SparK.Arbor.Gallery
variable {n:ℕ}
lemma defact (D: Fin n→ℕ)(u:(i:Fin n)→Label (D i))(v:Fin n→ℝ)(i j:ℕ)(hy:∀ k,wider C Q (u k) (v k) j i)(f:Fin n→ Cover)(hF:seaM C i j f)(hg:6*n<(C.S.step j).L.val)(hk:j+1 ≤ C.N i)(hC:C.Path β ν) : ‖metricP C Q D u i f‖≤ ∏ i,v i:=by
    let S:= cK; let P:= Q; let W:= Ω i; let K:= (C.S).side (C.R i) (C.N i)
    let g:=viewW cK (C.R i) hk; let g':=viewW cK (C.R i) (show j ≤ C.N i from Nat.le_of_lt hk); -- hk.le is j+1≤.. Less? h filter_ge_atTop returns j+1 ≤ C.N i, .le gives? `.le` parser with (<)`? Prop subtype.V fix.
    let t:=mural g' (evenW _ _ (hC.even i) _) (0:Site K); let F:=wrap K ∘ f
    have hPos:t.side.val= (ratioTo cK (C.N i) j):=rfl; let L:=Ratio.count g; let M:=6*n
    have hγ: n*(2*(3*L.val))<t.side.val:=by rw [hPos,step_factor hk, show n*(2*(3*L.val))= (6*n)*L.val by ring]; exact Nat.mul_lt_mul_of_pos_right hg L.pos
    obtain ⟨x,hx⟩:= t.fits_together F (3*L.val) (by positivity) hγ; let X:= t.newly x; let Y(k:Fin n):= X.which (F k); have hZ : Injective Y:= by
         intro i j he; by_contra ho; apply (not_le.mpr (hF i j ho)); let P':= (hx i).1; exact X.extent P' (show F j∈ X.chamber (Y i) from he.symm ▸ (show F j∈ X.chamber (Y j) from (hx j).1))
    let G(a:Fin n):= P.physical none i (u a) (f a); let Qa(a:Fin n):= floorL X W.average W (G a) (Y a); have hm(k:Fin n):= hy k hk X hPos rfl (Y k) (f k) (hx k); let P₁:= List.ofFn G; have hr:W.t=0:=rfl
    have hh: ‖W.average ((List.finRange n).map G).prod‖ ≤ ∏ i:Fin n,Qa i:= plant X W.average W rfl G Y hZ 0 _ (List.nodup_finRange n) (fun i=>List.mem_finRange i) (fun i=>(hm i).1) hr (averageSeal X W rfl (hC.normalized i|>.beta_pos (Nat.le_refl _) |>.le) (sideW hC i _) 0) (battery hC i)
    change ‖W.average (List.ofFn G).prod‖ ≤ _; rw [List.ofFn_eq_map]; exact hh.trans (prod_le_prod (fun i _=>floor_nn X W.average W ..) (fun i _=>(hm i).2))
end YM.Massive.Patria.Hub
#print axioms YM.Massive.Patria.Hub.defact
