import YM.QCD.High.Yang
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
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
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
open High PrismT MeasureTheory
abbrev Pixel (c:Side)(N:ℕ):= Grid c→EvenA c N
noncomputable def levit (c:Side)(N:ℕ):Fields c N→L[ℂ]EvenA c N:= LinearMap.toContinuousLinearMap (Cove.light (Keys c N)).toLinearMap.leftInverse -- implicit field
lemma callH (x:EvenA c N):levit c N (Cove.light _ x)=x:=by
    let T: EvenA c N→ₗ[ℂ] Fields c N:=(Cove.light _).toLinearMap; change T.leftInverse (T x)=x; apply LinearMap.leftInverse_apply_of_inj; exact LinearMap.ker_eq_bot.mpr (fun x y h=> Subtype.ext h)
lemma levyR (X:Fields c N)(a:ℝ): levit c N (a • X)=a • levit c N X := map_smul ((levit c N).restrictScalars ℝ) ..
lemma liftU (x:Pixel f N) (U:Grid f)(s:ℝ): can S h N (s • x) U=s • can S h N x U:=by
    unfold can; rw [show Cove.light _ ((s • x) U)=s • Cove.light (Keys f N) (x U) from map_smul ((Cove.light (Keys f N)).toLinearMap.restrictScalars ℝ) ..]; unfold Kit.sheath
    simp only [Complex.ofReal_one, inv_one,one_pow,one_smul]; -- complex smul re
    let A:= Modes f N; let B:=Modes c N; let v:= Cove.light (Keys f N) (x U); rw [show Grass.near A B (s • v)= _ from (map_smul ((Grass.near A B).toLinearMap.restrictScalars ℝ) ..)]; simp only [LinearMap.restrictScalars_apply,AlgHom.toLinearMap_apply, Algebra.smul_mul_assoc]; exact map_smul ((Grass.marginal A B).restrictScalars ℝ) ..
lemma beamG (c f:Side)(h:f.val=c.val*S.L.val) (x:Pixel f N)(q s:ℝ)(U:Grid c): advance S K h (s • x) q U=s • advance S K h x q U :=by
    unfold advance StepData.push; rw [← integral_smul]; simp_rw [liftU]; refine integral_congr_ae (ae_of_all _ fun i=>?_); exact smul_comm ..
noncomputable def fort (S:Flight j j)(K:KernelChoices)(h:f.val=c.val*S.L.val) (N:ℕ)(β:ℝ)(X:Pixel f N): Pixel c N:= levit c N ∘ advance S K h X β
noncomputable def vest (c:Side)(N:ℕ)(v:ℝ)(X:Pixel c N): Pixel c N:= wearK c N v ∘ X
lemma canonX (v₀ v₁ w u:ℝ)(hv:0<v₀)(hu:0<v₁) (P: Pixel f N)(X Q:Pixel c N) (hΞ:vest c N v₁ X= Q)
    (hp:∀ A,advance S K h P β A=u • gBody c v₀ (X A)): vest c N (v₁*v₀) (fort S K h N β (w • P))=(w*u) • Q ∧∀ U,advance S K h (w • P) β U=Cove.light _ (wearK c N (v₁*v₀)⁻¹ (((w*u) • Q) U)):=by
      let x (U:Grid c):= fort S K h N β (w • P) U; have hx(U:Grid c): x U=w • (u • wearK c N v₀⁻¹ (X U)):=by unfold x fort; dsimp only [Function.comp_apply]; rw [beamG, hp, levyR, levyR,callH]
      have hs(U):wearK c N (v₁*v₀) (x U)= ((w*u) • Q) U:=by
         let y:=wearK c N v₀⁻¹ (X U); have hm : wearK c N (v₁*v₀) y=Q U:=by
              have he :((v₁*v₀)*v₀⁻¹)=v₁:=by field_simp
              exact (show _=wearK c N ((v₁*v₀)*v₀⁻¹) (X U) from Subtype.ext (Kites.makes _ _ _)).trans ((by rw [he] : wearK c N _ _=wearK c N v₁ (X U)).trans (congr_fun hΞ U))
         rw [hx]; let M:=songT (c:=c) (N:=N) (v₁*v₀); rw [show wearK c N _ (w • u • y)=w • u • wearK c N _ y from (by change M (w • u • y)=w • u • M y; rw [map_smul,map_smul]), hm]; exact (mul_smul ..).symm
      refine ⟨funext hs,fun U=>?_⟩; rw [← hs U,wit _ _ _ (inv_mul_cancel₀ (mul_pos hu hv).ne'),hx U,beamG,hp]; let A:= ((Cove.light (Keys c N)).toLinearMap.restrictScalars ℝ)
      exact ((A.map_smul w (u • _)).trans (congr_arg (w • ·) (map_smul A u (wearK c N v₀⁻¹ (X U))))).symm
-- L timeline canonical sign sign.B.Tech
end Rails
end YM.QCD.Acre
