import YM.QCD.Suns.Mirage
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open NormedSpace
lemma sunpow {I:Type} {g:I→ℝ}(hv:SumBudget g v):SumBudget (fun x: Finset I=>∏ i∈x,g i) (Real.exp v):=by
    let f (i:Finset I):= if i=∅ then (1:ℝ) else 0; have hm:Summable f:=summable_of_ne_finset_zero (s:={∅}) (fun i hi=>by simp_all [f]); have he:SumBudget f 1:=⟨fun i=>by unfold f; split <;> simp_all,hm,(show ∑' i,f i=1 from (tsum_eq_single ∅ (fun _ h=> if_neg h)).trans (if_pos rfl)).le⟩
    let X (i:Finset I):= if i.Nonempty then ∏ j∈i,g j else 0; rw [show (fun i:Finset I=>∏ j∈i,g j)=fun i=> X i+f i from funext fun i=> by by_cases h:i=∅ <;> simp [X,f,nonempty_iff_ne_empty,h]]; exact (sub_add_cancel (Real.exp v) (1:ℝ)) ▸ sumBudget_add (sumBudget_exponential hv) he -- hp
lemma spiritual (g:I→ℝ)(f:I→Support c)(he:Ac.Hit f k g u v)(h:∀ i,(f i).Nonempty)(hr:0≤u)(hp:∀ i,0≤g i): SumBudget g (↑(Fintype.card (Site c))*v):=by
    have hh:= budget_over (univ:Finset (Site c)) _ _ (fun x _=> he x); simp only [sum_const,card_univ,nsmul_eq_mul] at hh
    refine budget_mono hh hp fun i=>?_ ; obtain ⟨x,hx⟩:= h i; apply le_trans _ (single_le_sum (a:=x) (fun j (_ : j∈(univ:Finset (Site c)))=> (he j).1 i) (mem_univ x)); dsimp only; rw [if_pos hx]; exact le_mul_of_one_le_right (hp _) (Real.one_le_exp (mul_nonneg hr (by positivity)))
local notation "S₀"=> Fintype.card (Site c)
lemma wordy (b:Flavor N)(W:Voice c N)(h: Enn P b L x η β (duo W.P W.K)) (hp:P.B=highR L x)(U:Grid c): let G':=songT (c:=c) (N:=N) (fan L η x)⁻¹
     ‖heartK W.K P.threshold U‖ ≤ ‖G'‖*Real.exp (S₀:ℝ) ∧ ‖Patron.total W.P P.threshold U‖ ≤ ‖G'‖*((S₀:ℝ)*Jets.Touch.chip L x):=by
    intro G'; have he := Rain.panel b W h hp U; obtain ⟨f,g,hΓ,hY⟩:=h; have hX:= hΓ.fillP.ε
    let Y:=duo W.P W.K; let K:=Ruby.tK W.K P.threshold U; let r:=taxK L x 1; have hs:1 ≤ r:=Real.one_le_exp (mul_nonneg zero_le_one (fan_pos ..).le); have ht (i:W.β):= hΓ.centsP.non i; have hx(i:W.β): g i ≤ g i*r^(Y.front i).inv.card:=le_mul_of_one_le_right (ht _) (one_le_pow₀ hs)
    have hh:= budget_mono (spiritual (I:=W.β) _ (fun i=>(Y.front i).place) hX (fun i=> (Y.front i).alive.mono (Y.front i).part) hΓ.fillP.bud (fun i=> (ht i).trans (hx i))) ht hx; rw [mul_one] at hh -- ok
    let t:= fan L η x; let F:=songT (c:=c) (N:=N) t
    have hu (i:Finset W.β): ‖F (K i)‖ ≤∏ j∈i,g j:=by
         unfold K Ruby.tK; split
         next h=> change ‖Loom.token c N t _‖ ≤ _ ; refine (Loom.folkl ..).trans (prod_le_prod (fun _ _=>norm_nonneg _) fun k _=> hΓ.centsP.funds k U)
         next he=> rw [map_zero,norm_zero]; exact prod_nonneg fun i _=>ht i
    have hm:= budget_mono (sunpow hh) (fun _=>norm_nonneg _) hu
    have hw(i):G' (F i)=i:=wit i _ _ (inv_mul_cancel₀ (fan_pos ..).ne')
    refine ⟨?_,(show _ ≤ _ from (le_trans ((congr_arg norm (hw (Patron.total W.P P.threshold U))).symm.le) ((G'.le_opNorm _).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _)))))⟩
    let Z:= ∑' i,F (K i); have hz:= hm.2.1; have hF := hz.of_norm.hasSum; have hc:= G'.hasSum hF; change ‖∑' i,K i‖ ≤ _; refine le_trans (le_of_eq ?_) ((G'.le_opNorm Z).trans (mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hz).trans hm.2.2) (norm_nonneg _))); apply congr_arg; exact (tsum_congr (fun i=> (hw (K i)).symm)).trans hc.tsum_eq -- infer
end Rails
end YM.QCD.Acre
