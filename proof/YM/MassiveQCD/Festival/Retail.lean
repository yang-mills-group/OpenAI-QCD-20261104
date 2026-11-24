import YM.MassiveQCD.Festival.Layer
/-! # Ports for tilted log commuting before assembling a Cents layout
 Keep arbitrary P.t.order, lemma costs have `window`. Zero π still gives all masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Festival
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae Stem Stew Stew.Phased
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n:ℕ} {a r u t σ τ η ξ T θ x:ℝ}{p:BudgetPoint}{o:Site c}
open Villa Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Jets.Touch Kites
variable {I J K K₀:Type}
open Ruby Ruby.LanternK Acre Acre.Rails
open Stew.Phased Villa Ruby.LanternK
open MassiveQCD.Analysis.Many MassiveQCD.Analysis
variable (G:Gem c N I)(X:Patron.Rail c N J)(z:ℂ)
namespace Layer
variable (M:Layer c N I K J)(A:BudgetPoint)
variable (b:Flavor N)
local notation "M?"=>M.prepare
noncomputable def choir (z:ℂ):= Reggae.weave M.base (M.costumes z)
lemma route_I (x:ℂ): (M?).get x=duo (M.choir x) (M.mask x):=rfl
-- do zero λ represent EXACT Mask colors. Qi.Paper from Orchestra.Board.
variable (hQ : Hill M b p t η τ ξ T θ)
include hQ
lemma zerod (x:(Site c⊕ K)×Rays): (M.costumes 0).view x=0:= renounces M.sheet M.crown x.1 x.2 (stamp M b hQ |>.2 x.1 |>.1) -- order
omit hQ
lemma hap (hp:Keyed G)(hv:∀ i,G.view i=0)(he:0≤ t) : Capacity G b p t η 0:=by
    have hh i:= Moss.freeK (B:=p) (n:=N) (t:=t) (G.addr i).site (G.addr i).support; let X:=hp.notes;
    refine ⟨⟨{ gauge:=X.gauge,real:=X.real,num:=?_ },hp.turns⟩,(fun _=>0),fun i=>?_,fun i=>?_⟩ -- ∃ parentheses syntax
    · intro i V k hk; rw [hv, Pi.zero_apply,map_zero]
    · have hu : (fun j=> if (G.addr j).site=i then (0:ℝ)*Real.exp (η*coverNumber p.B (G.addr j).support) else 0)=fun _=>0:=funext (fun j=>by split<;>simp); exact hu.symm ▸ (show SumBudget (fun _:I=> (0:ℝ)) 0 from ⟨fun _=>le_rfl,summable_zero,by simp⟩)
    refine ⟨(hv i).symm ▸ hh i,fun hx=>?_ ⟩ -- rewrite direction inverted
    have hA: Woven (G.addr i).site (G.addr i).support p t (G.view i) 0:= (hv i).symm ▸ hh i
    have hu: (Reggae.river c N) ∘ (G.view i)=fun _=>0:=by rw [hv]; funext U; exact map_zero _
    refine ⟨hA, X.gauge i, fun V k hh=>?_, X.real i, ?_, (spores _ _ _ hA (X.gauge i) he).1, (G.addr i).anchor, ?_,fun _ x y _ _=>?_⟩
    · rw [hv,Pi.zero_apply,map_zero]
    · intro x; rw [hv]; exact ( (profile (G.addr i).site x).comp (meter b)).map_zero
    · rw [hu]
    rw [hu]; exact AnalyticBridge.VerifiedReset.hessian_zero ..
-- canonical-weigh W.BASIS aligned.Not REQUIRE control tagE.Stretches when real by continuous maps. 
lemma crossZero (R: Gem c N K)(he:Capacity G b p t u a)(hf:Capacity R b p t u r):Capacity (Reggae.weave G R) b p t u (a+r):=by
    obtain ⟨f,h,hv⟩:=he.book; obtain ⟨g,hg,hG⟩:= hf.book; exact ⟨Reggae.pilot _ _ he.basis hf.basis,⟨Sum.elim f g,fun i=> Extra.Iteration.Cost.sum (h i) (hg i),fun i=>by cases i <;> first | exact hv _ | exact hG _⟩⟩ -- palette quotes
include hQ
lemma scrip (ht:0≤ t): Capacity (M.choir 0) b p t η τ:=by
     have he:= oriented M.sheet M.crown (Layer.stamp M b hQ).1 0; rw [Complex.ofReal_zero] at he; exact add_zero τ ▸ (crossZero _ b (M.costumes 0) hQ.asleep (hap _ _ (woke _ _ he) (fun i=>zerod M b hQ i) ht)) -- args
variable (hx:1≤ t)(hz: T≥1)(g:Site c⊕K→ℝ)(hr:∀ i,Woven (M.sheet.addr i).site (M.sheet.addr i).support p t (M.sheet.view i) (g i))(hp:∀ i,2^p.order*g i ≤1/4)(hy:‖z‖≤1)
omit hQ
include hx hr hp
lemma graduate : (M?).Scale p.threshold :=by
     constructor
     · rintro i hi (j|⟨u,w⟩) V; · change NormedSpace.exp (masked p.threshold _ _ _) -1= i^0 • _; rw [pow_zero,one_smul]; rfl
       have h z : ((M?).get z).reading p.threshold V (Sum.inr (u,w))=masked p.threshold (M.sheet.addr u).support (plyM (M.sheet.view u) (z^M.crown u) w) V:=rfl
       rw [h,h]; nth_rw 1 [show (M?).generation (Sum.inr (u,w))=M.crown u * Many.tier w from rfl]
       have hv : ‖i^M.crown u‖≤1:=by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hi
       by_cases hV:Healthy p.threshold (M.sheet.addr u).support V
       · rw [masked_eq _ _ _ _ hV, heatExp _ _ V hV (hr u) hv (hp u) hx,masked_eq _ _ _ _ hV,one_pow, heatExp _ _ V hV (hr u) (by simp) (hp u) hx,pow_mul,one_pow,one_smul]; abel
       rw [masked_ne _ _ _ _ hV,masked_ne _ _ _ _ hV,NormedSpace.exp_zero,sub_self,smul_zero]
     intro a h i p; change a^M.degree i • M.forced.warp i p=a^M.degree i • ((1:ℂ)^M.degree i • M.forced.warp i p); rw [one_pow,one_smul]
include hy
lemma fairLaunch (Z:Grid c) (hV:Summable (letters M.base p.threshold Z)) (x:ℝ)(h:Anchored (fun i=>(M.sheet.addr i).site) g (fun i=>coverNumber p.B (M.sheet.addr i).support) η x)(hh:0≤η) (U : St c)(s: Grid c→ℝ): scoreV (M.choir z) (M.mask z) p.threshold s U Z=M.issue p.threshold s U z Z:=by -- order Z
     have hf:HasSum (letters (flagE M.sheet M.crown z) p.threshold Z) (Patron.total (M.costumes z) p.threshold Z):=tuneTotal M.sheet M.crown z g h hr Z hp hx hy hh
     have hA: Summable (letters (M.costumes z) p.threshold Z):= permits (M.costumes z) (show Licence p η _ t _ from ⟨ priceM p.order g, seatsT M.sheet M.crown z g h, candles M.sheet M.crown z g hr hp hx hy⟩) (zero_lt_one.trans_le hx) hh _
     unfold issue choir pub scoreV heartS; rw [Reggae.woven_sum _ _ _ hV hA,Reggae.woven_sum _ _ _ hV hf.summable,show Patron.total (flagE M.sheet M.crown z) p.threshold Z= _ from hf.tsum_eq] -- last hf.tsum is Alt.W instead of total defeq
end Layer
end YM.QCD.Festival
