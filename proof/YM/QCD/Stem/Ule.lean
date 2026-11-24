import YM.QCD.Stem.Orbit
/-! # Purchases w constants per eventual.Clusters. -/
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
variable {C:Side}{D D' w j k l:ℕ}{d r t t' p p' η b z A Δ θ ρ P':ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove YM.Next.Scheduling Footprint Moss Extra.Iteration Song Meadow Quotes
variable (S:PathData su)(O:Clip)(W: ℕ→Atom su j)
local notation "R"=> sax S O B c N t p
local notation "F"=> codaX W N p c
local notation "q₀"=>B.B
local notation "K"=> keepP S c B.B
local notation "A₀"=> preExponent B
lemma opticX (U:EvenA c N)(x:Site c)(η:ℝ)(h:0<η): ‖Loom.token c N η U‖ ≤ Sen x η U:=shot (lens x) U.val η h
lemma peg_pos: 0<(A₀):= by unfold preExponent; linarith [B.exponent_pos]
lemma sproutsP (V:Grid c)(ht:S.Bounds O r d p') : income (R) B.threshold V=baker c N (tells S O B t p V):=(swell S O B ht V).tsum_eq
lemma lodgeK (ht:S.Bounds O r d p') (hC:WilsonStartup.Decent O B) (he : 1≤η)(hw:preExponent B/B.B≤r/4)(hk:0<b)(hh:0 ≤ z):∀ᶠ m in atTop,
    let T:= sax S O B c N t p; let u:=2*B.B
    let C:=Song.octaveNeed su B O r d p' t p
    Bound (tuckS T (K m) u) univ (huskQ T (K m)) (burl T (K m) u B) B (u+u) (Real.exp (-(r/4)*B.B)*C+b) (C*ballCost u) (penS u 2 C z) η A₀ z (income T B.threshold):=by
    obtain ⟨hz,H⟩:= enough (c:=c) (N:=N) (t:=t) (p:=p) S O ht hC (zero_le_one.trans he) hw
    have hf :0≤ r/4:=div_nonneg ht.width.le (by norm_num)
    filter_upwards [skyline R _ H hf (fun i x=> x∉ K i) hk (fun j h=> (upward S j (n:=B.B) h).mono fun m hm=> not_not_intro hm)] with m hm
    intro T u C; exact infold T (K m) (turtle T _ H hf) hz (w:=2*B.B) (fun i h'=>by rw [two_mul]; exact keptP S O B _ h') hm he peg_pos.le hh le_rfl
local notation "Q"=> joinP c W B.B
set_option maxHeartbeats 200000 in
lemma comic (ht:Charged W r A) (hC:SymmetricAtoms W)(hp:0<r)(he:1≤η)(hw:preExponent B/B.B≤ r/4)(hk:0<b)(hh:0 ≤ z)(hv:z+1+1≤ preExponent B): ∀ᶠ m in atTop,
   let T:=codaX W N p c
   let D:= anchoredFee (Song.headline B) (Song.octave j)* Song.tenor su j B r A (-p)
   let G:= anchoredFee (Song.headline B) (Song.octave j)*(|VerifiedReset.factor*(-p)| * 2^j*A)
   Bound (tuckS T (Q m) q₀) univ (huskQ T (Q m)) (Ruby.HJoin (burl T (Q m) q₀ B) (hoist T B.threshold)) B (q₀+q₀) (Real.exp (-(r/4)* q₀)*D+b) (D*ballCost q₀) (penS q₀ 1 D z+Footprint.payment 1 (4*q₀+2) 0 1 1 G z 0) η A₀ z (fun V=> baker c N (p*Extra.Iteration.action W V)):=by
   obtain ⟨hZ,H⟩:= leaning (N:=N) (c:=c) (b:=p) W ht hp hC (zero_le_one.trans he) hw
   have hf:0≤r/4:= div_nonneg hp.le (by norm_num)
   filter_upwards [skyline F _ H hf (fun i x=> x∉ Q i) hk (fun j h=> (reached W j (w:=q₀) h).mono fun m hm=> not_not_intro hm)] with k hk'; intro T D G
   have hz:= turtle T _ H hf
   have ht':= infold (b:=A₀) T (Q k) hz hZ (fun i hi=> (show (T.addr i).support ⊆ neighbors q₀ i.1.2 from scarves W i hi)) hk' he peg_pos.le hh (show q₀≤1*B.B from by rw [one_mul]) -- t?
   let x i:= heftL W p ((i:Stave (n:=c)).2); have hx:Anchored (fun i=>(T.addr i).site) x (fun i=>coverNumber B.B (T.addr i).support) A₀ G:= megaT W ht hp (le_trans hw (by linarith)) -- hp threshold enough
   have he':0 < η:=zero_lt_one.trans_le he
   have hc:∀ (i:Stave (n:=c)) (U:Grid c),‖Loom.token c N η (T.view i U)‖≤ x i:=by
       intro i U; exact (opticX (T.view i U) (T.addr i).site η he').trans (tollT W U i he'.le)
   have hV:= stony T hz hZ he' x hx hc hv hh
   exact away _ _ _ _ ht' he peg_pos.le _ hV hh (fun _=> Summable.of_finite) (fun V=> thaw T hz he peg_pos.le V _ (shuns W V ht hp))
end YM.QCD.Stem
