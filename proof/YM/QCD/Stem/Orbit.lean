import YM.QCD.Stem.Stilt
/-! # harvest composition typing. Between this step and EARLY:
 Fit tags canonical vs syn Outlet. Low at peeled all V.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stem
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure Precision ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove AnalyticBridge VerifiedReset
variable {C:Side}{D D' w j:ℕ}{d r t t' p p' η b z A Δ θ ρ P':ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove YM.Next.Scheduling Footprint Moss Extra.Iteration
variable (S:Gem c N I)(X:Finset I)(G:Gem c N J)(V':Ruby.Hue c N V)
abbrev huskQ (S:Gem c N I)(X: Finset I): Gem c N I:=Moss.muteK S (fun i=>i∉X)
local notation "p'₀"=>B.threshold
lemma sits (U:Grid c) (h:Summable (letters S B.threshold U)) : Patron.total S p'₀ U=(∑ i ∈ X,letters S p'₀ U i)+Patron.total (huskQ S X) p'₀ U:=by
   let f i:= letters S p'₀ U i; let g i:= if i∈ X then f i else 0
   have he : HasSum g (∑ i∈X,f i):=by
       convert hasSum_sum_of_ne_finset_zero (s:=X) (f:=g) (fun i hi=>if_neg hi) using 1; exact sum_congr rfl fun i hi=> (if_pos hi).symm
       infer_instance
   have hp : Patron.total (huskQ S X) p'₀ U= Patron.total S p'₀ U- ∑ i∈X,f i:=by
       refine ((h.hasSum.sub he).congr_fun fun i=>?_).tsum_eq
       change letters _ _ U i=f i-g i; rw [huskQ,masking]; by_cases he:i∈X<;>simp [g,f,he]
   rw [hp]; unfold f; abel
noncomputable def income (S:Gem c N I)(v:ℝ):= Patron.total S v
lemma infold (h:Licence B p d r S)(hg:Dyed S)(hs:∀ i∈X,(S.addr i).support⊆ neighbors w (S.addr i).site)(hf:Licence B b Δ r (huskQ S X))(hr:1≤r)(hp:0≤p)(hb:0≤t)(hz:w ≤ n*B.B) : Bound (tuckS S X w) univ (huskQ S X) (burl S X w B) B (w+w) Δ (d*ballCost w) (penS w n d t) r b t (income S p'₀):=by
    obtain ⟨hx,hV⟩:= ridden S X w h hg hs hp; refine ⟨hx,hV,hf,dyedM S hg _,outport _ w (fun _=>rfl) (paleness S X w h hg hs hp (zero_lt_one.trans_le hr)) hb hz,fun V=>?_⟩
    rw [income, sits S X V (permits S h (zero_lt_one.trans_le hr) hp V), riversQ,tsum_fintype]; abel -- args
lemma away {U U':Grid c→EvenA c N}(h:Bound S X G V' B w d r p p' b z U)(hp:1≤p')(hs:0 ≤ b) (M:Ruby.Hue c N J) (hr:TokenB M B.threshold B.B z A p') (hv:0≤z) (hm:∀ U, Summable (fun i=> V'.mean i U))(hU:∀ V:Grid c, HasSum (fun i=> M.mean i V) (U' V-U V)): Bound S X G (Ruby.HJoin V' M) B w d r (p+A) p' b z U':=by -- V':J' join V use J only; need different ν here e.g. G same high? χ I yes
     refine ⟨h.tilled,h.rip,h.loom,h.deed,strew V' M h.cash hr,fun W=>?_⟩
     rw [show (∑' i, (Ruby.HJoin V' M).mean i W)=_ from (HasSum.sum (f:=fun i=>(Ruby.HJoin V' M).mean i W) (hm W).hasSum (hU W)).tsum_eq,h.earns W]; abel
lemma tied {U:Grid c→EvenA c N}(h:Bound S X G V' B w d r p p' b z U)(hp:w ≤ n) : Bound S X G V' B n d r p p' b z U:={ h with tilled:= Grove.opensP S X h.tilled hp } -- order X/g
lemma thaw (h:Licence B t p r S)(hv:1 ≤ r)(hp:0≤t) (U:Grid c)(x:EvenA c N)(he:HasSum (fun i=> S.view i U) x):HasSum (fun i=>(hoist S p'₀).mean i U) (x-(income S p'₀) U):= he.sub (permits S h (zero_lt_one.trans_le hv) hp U).hasSum
end YM.QCD.Stem
