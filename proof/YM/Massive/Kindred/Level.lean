import YM.Massive.Kindred.Permute
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
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open Grass


open Grass Patron
variable (A: Voice f N) (i₀:Flavor N) (T) (B: Badge P₀ τ R P o χ T U b (run S.L x) r β μ z)


local notation "δ'"=> α+(N:ℝ)*ν
open Struck Library Weft Fibre
namespace Kin
open Aperture Bank Conductor Conductor.Quant MeasureTheory Sway OrbitG
open Finset Pith Aperture
open scoped Classical
variable (s: Equiv.Perm (Flavor N))
open Function MeasureTheory Pith High PrismT NormedSpace Massive.Filament
variable (L)
abbrev LanternT (n:Side)(N:ℕ)(c:Side) := EvenA n N→ₗ[ℂ] Lanes c N
variable (T: LanternT f N c)
-- T ties startup global source EvenA input, transport analytic & unnormal.Rep.Y.Supplier. operator is linear-in-insertions; evaluated output exactly at arbitrary points.
structure Tied (T: LanternT f N c):Prop where
    crewT (x:EvenA f N)(L:Matrix (Flavor N) (Flavor N) ℂ)(h:L∈unitary _): crew N L (T x) (T (Wheel N L f x))
-- mass observer.: x monetary. value as continuous operator
noncomputable def wind (U:Grid c): EvenA f N→L[ℂ] EvenA c N:=LinearMap.toContinuousLinearMap {toFun:= fun x=> T x U,map_add':=fun i j=> by rw [T.map_add]; rfl,map_smul':=fun i j=>by rw [T.map_smul];rfl} -- hd syntax change.V.Point
variable (u : Flavor N→ℝ)
abbrev experimental (α:ℝ)(z:ℂ) (U:Grid c): EvenA c N := T (exp (((α:ℂ)*z) • ingredient f u)) U
lemma experimentalV (α:ℝ): experimental T u α 0=⇑(T (1: EvenA f N)):=by funext i; simp [experimental]
variable (b: Flavor N)(A':EvenA c N)
abbrev g0 := T (1: EvenA f N) (1:Grid c)
noncomputable def loanR : EvenA c N →L[ℂ] Sheet c:= (clay c N).smulRight ((-(clay c N A')⁻¹^2) • ((Stew.meter b) A')) + (clay c N A')⁻¹ • Stew.meter b
lemma loanAp (X:EvenA c N) : loanR b A' X=(-mud X / mud A'^2) • feeF b A'+(mud A')⁻¹ • feeF b X:=by
   unfold loanR; change mud X • ((-(mud A')⁻¹^2) • (feeF b A')) +  (mud A')⁻¹ • feeF b X=_; rw [smul_smul]; congr 2; rw [inv_pow]; ring
set_option maxHeartbeats 850000 in
lemma currency (X₀ Y Z:EvenA c N) (hp:Wheel N (Stew.spin s) c X₀=Z) (hz:Wheel N (Stew.spin s) c Y=Y)(h:Phases X₀)(hY:Phases Y): loanR (s b) Y Z=loanR b Y X₀:=by
   let L:= Wheel N (Stew.spin s) c; have h1: feeF (s b) Z=feeF b X₀:=(congr_arg (feeF (s b)) hp.symm).trans (pivotW s b X₀ h); have h2: feeF (s b) Y=feeF b Y:=(congr_arg (feeF (s b)) hz.symm).trans (pivotW s b Y hY)
   have h: mud Z= mud X₀:= (congr_arg mud hp.symm).trans (Reggae.walks X₀ _)
   rw [loanAp,loanAp,h,h1,h2]
lemma pressK (Y:ℂ→EvenA c N) (X:EvenA c N)(he: HasDerivAt Y X 0)(hv:mud (Y 0)≠0): HasDerivAt (fumes b ∘ Y) (loanR b (Y 0) X) 0:=by
    have hp := ((clay c N).hasFDerivAt.comp_hasDerivAt 0 he).inv (show (clay c N ∘ Y) 0≠0 from hv); have hY:= (Stew.meter b (c:=c)).hasFDerivAt.comp_hasDerivAt 0 he; rw [loanAp,add_comm]; exact hp.smul hY -- check order
lemma gear_exp (u: ℝ)(V:EvenA f N): HasDerivAt (fun z:ℂ=>exp (((u:ℂ)*z) • V)) ((u:ℂ) • V) 0:=by
    have h:HasDerivAt (fun z:ℂ=>exp (z • ((u:ℂ) • V))) ((u:ℂ) • V) 0:=by simpa using hasDerivAt_exp_smul_const ((u:ℂ) • V) (0:ℂ)
    rw [show (fun z:ℂ=> exp (((u:ℂ)*z) • V))= _ from funext (fun z=> (show exp (((u:ℂ)*z) • V)=exp (z • ((u:ℂ) • V)) from (by rw [smul_smul,mul_comm z])) )]; exact h -- parser `from funext …` elaborator let? simplify
variable {t:ℝ} (a:ℝ) -- b orientation head same?
set_option quotPrecheck false
local notation "φ"=> Rotary.chartR x
variable (hv:mud (g0 T)≠0)(hh:Tied T)
include hv
lemma beadLens : Massive.Filament.bead 1 (fun z=> fumes b (grow (Rotary.chartR x) (experimental T u a) z 1))=(a*φ:ℝ) • loanR b (g0 T) (T (ingredient f u) 1):=by
    let Y z:= grow (Rotary.chartR x) (experimental T u a) z 1; let W:= wind T 1; let f':=ingredient f u; let r:=(a*φ:ℝ);
    have he:Y=W ∘ (fun z:ℂ=> exp (((r:ℂ)*z) • f')):= by funext z; change T (exp (((a:ℂ)*((Rotary.chartR x:ℂ)*z)) • ingredient f u)) (1:Grid c)= T (exp (((r:ℂ)*z) • f')) (1:Grid c); unfold f' r; rw [Complex.ofReal_mul, mul_assoc];
    have hY:Y 0=g0 T:=by rw [he,Function.comp_apply,mul_zero,zero_smul,exp_zero];rfl
    have hd :HasDerivAt Y ((r:ℂ) • (W f')) 0:= by rw [he,← map_smul]; exact W.hasFDerivAt.comp_hasDerivAt 0 (gear_exp r f');
    have hF:= (pressK b Y _ hd (hY.symm ▸ hv)).deriv; rw [bead_first]; change deriv (fumes b ∘ Y) _=_; rw [hF,hY,map_smul]; rfl
noncomputable def flagL : Sheet c→ₗ[ℝ]ℝ:= (Fintype.card (Site c):ℝ)⁻¹ • (Complex.reCLM.comp ((Finch.stowL c).restrictScalars ℝ)).toLinearMap
omit hv in
lemma gflag (U:Sheet c): flagW U= flagL U:=by change _= (Fintype.card (Site c):ℝ)⁻¹ *(stow U).re; rw [Finch.far]; field_simp
noncomputable def profit (η x:ℝ):(Flavor N→ℝ) →ₗ[ℝ] (Flavor N→ℝ):= LinearMap.pi fun b=> ((fan L η x)^2*(Rotary.chartR x)) • (flagL.comp (((loanR b (g0 T)).comp (wind T 1)).toLinearMap.restrictScalars ℝ) |>.comp (race f N)) -- under Caps `wind`. 
lemma goldBook : hear L (experimental T u a) η x b=a*(profit L T η x u b):=by unfold hear Sens; rw [beadLens T u b a hv,gflag,map_smul]; change _= a*(((fan L η x)^2*(Rotary.chartR x)) * flagL (loanR b (g0 T) (T (ingredient f u) 1))); simp only [smul_eq_mul]; ring
omit hv
include hh
lemma modesBright (z:EvenA f N)(p: Matrix (Flavor N) (Flavor N) ℂ)(hp:p∈unitary _)(he:Wheel N p f z=z)(V:Grid c): Wheel N p c (T z V)=T z V:=by have hh:= hh.crewT z p hp V; rw [he] at hh; exact hh
lemma blinding (i:Flavor N): profit L T η x (draw s u) (s i)=profit L T η x u i:=by
    let H(u:Flavor N→ℝ):= T (ingredient f u) (1:Grid c); let L₀:= Stew.spin s; let Z:= g0 T; let W:= draw s u
    have he : Wheel N L₀ c (H u)= H W:=by rw [show H W= _ from congr_arg (fun F: EvenA f N=> T F (1:Grid c)) (Kin.center (c:=f) s u).symm]; exact hh.crewT _ _ (Stew.spun s) 1
    have ht(f:EvenA f N)(h:Phases f): Phases (T f (1:Grid c)):= fun p hp=> modesBright T hh f _ hp (h p hp) _; -- arg.N
    have hF:Phases (H u):= ht _ (scout u); have h0:Phases Z:= ht _ phase_id
    have hZ : Wheel N L₀ c Z=Z:= modesBright T hh 1 _ (Stew.spun s) (map_one _) _
    have hk:= currency s i (H u) Z (H W) he hZ hF h0
    let y:=(fan L η x)^2*Rotary.chartR x; change y*flagL (loanR (s i) Z (H W))=y*flagL (loanR i Z (H u)); rw [hk]
-- p::implicit.Geometry.Φ.S.
include hv
lemma arcT (A:Arrow N)(hp: (∑ i,A.tip i)=0)(hN: 2≤N): ∀ z:ℝ, let F:=experimental T A.tip z; Pinned F (Rotary.chartR x) (fan L η x) A (hear L F η x A.head) :=by
   intro z H₀; obtain ⟨p,hp'⟩:= orients (profit L T η x) (fun s u i=>blinding L s T u hh i) hN
   intro i; change hear L _ _ x i=(hear ..)*A.tip i; unfold H₀; rw [goldBook L T _ _ z hv,goldBook L T _ _ z hv,hp' _ hp,hp' _ hp,A.has_one,mul_one,mul_assoc] -- arg order test
end Kin
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Kin.arcT
