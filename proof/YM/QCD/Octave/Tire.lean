import YM.QCD.Octave.Hilt
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Octave
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam Cove Golden NormedSpace
open scoped Topology ENNReal ContDiff BigOperators Classical
open Lat YM.Next.Free Reggae
open Jets.Touch Port Kit Run Stew Bay Strut Leaf Tee Flume Garden Kings Orbit LeafM
open Revolve
open Loom Fleet
open AtomF
open Loom Fleet AtomF Oasis
open Oasis
variable {σ C P' p Z v ξ θ ζ w σ' C' e Δ p' ν:ℝ}{K: KernelChoices}{P : Teller su}{l N j k:ℕ} {g:ℝ→ℝ}
-- j arbitrary requested order; height tech depends on l. Choose universal fixed n MAT version.
def Font (j:ℕ)(ξ θ v ζ:ℝ):Prop := 0 <θ∧ θ*2<v ∧ v<ξ ∧ ξ <1 ∧ amass (j+1) ξ (2*(θ*2+ξ*2)) < ζ
lemma leases (j:ℕ)(ζ:ℝ)(hv:0<ζ): ∃ ξ θ v:ℝ, Font j ξ θ v ζ:=by
   let f t:=amass (j+1) t (2*(t/8*2+t*2)); have he:f 0=0:=by simp [f,amass,heron]
   have h : Continuous f:=by unfold f amass heron; fun_prop
   have hb : ∀ᶠ x in 𝓝[>](0:ℝ), f x<ζ:= (h.continuousAt.continuousWithinAt (x:=0)).eventually (gt_mem_nhds (he.trans_lt hv)) -- edit
   have hp : ∀ᶠ x in 𝓝[>](0:ℝ), 0<x:= self_mem_nhdsWithin (a:= (0:ℝ)) (s:=Set.Ioi 0)
   obtain ⟨z,⟨hz,he⟩,hI⟩:= ((hp.and hb).and (nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1)))).exists; change 0 < z at hz; exact ⟨z,z/8,z/2,by unfold Font; exact ⟨by positivity,by linarith,by linarith,hI,he⟩⟩

section coast
open scoped Matrix.Norms.Frobenius
variable (Q:ConnectedActivityE6.Target su P)
lemma verdant (F':Plan j) (S:Patch)(V:Before su σ C S.J K ((l+1+2)+3))(E:FiberFee Q.table (((l+1+2)+3)+1)) (Y:BareRates.pre su σ' C' ((l+1+2)+3)) (hp : Bolt su S.L g)(b b':Clip) (hm:Font l ξ θ v ζ)(o: ConnectedActivityE6.Target.Order su P') (hs:0<e)(a A d B r D K':ℝ)(hx:0<a)(hy:0<d)(hr:0<r)(hκ:0<K'): ∀ᶠ x:ℝ in atTop, ∀ (c f :Side)(G:Flight j k)(h:f.val=c.val*G.L.val)(I:StepData c f)(F:Forest I.ratio)(T: Tube su I)(he:I.patch=S)(hK:I.kernel=K)(β:ℝ)(R R':BudgetPoint),G.L=S.L→T.high=b→T.low=b'→Quilt T F (g x)→ T.up.Bounds b σ C Z → T.up.Bounds b σ C (ConnectedActivityE6.loopBill su S.L x)→ T.down.Bounds b' σ' C' w →R'.threshold=Pressure.temp x → ∀ (ρ:Bid.Dir su c→AxisChart su F), (Sienna.warm V he hK).Service F T.high T.up ρ→ClassicalMatch F T.high T.low T.up T.down ρ→∀ (i:I.Choices) (X:Coat T F)(u:ℝ), X.x=x→ X.width=o.K→ Cash P' x e S.L Q o u T (Pane.virgin T R β)→ X.manifest→ RG.flags (Pressure.temp x) X.V=∅→∀ W:Positions (Uniform.Primary c su), X.V=represent (tint su _ W)→‖W‖+furl su S.L x<eaves su S.L x → ∀ (J:Offer 1 a A)(U:Offer 2 d B)(θ':ℕ→Atom su 2),Extra.Iteration.Charged θ' r D→ Extra.Iteration.SymmetricAtoms θ'→∀ p:ℝ, |p|≤wink S.L x→ let K₀:=park G h F' J U (haloK S.L x) p; let G':= tonic h K₀ θ' N (highW S.L K' θ x) ∘ F.drape
     0 < tramp T R β W ∧ Brush l (brass S.L x ζ) (eaves su S.L x)⁻¹ (Sol (G:=su) (N:=N) β F T R (Oasis.heat G' (Lapis.orbit F ρ))) W := by
   obtain ⟨hθ,h₁,h₂,h₃,hM⟩:=hm; have hv:0 < v:=lt_trans (by positivity : 0<θ*2) h₁; have he':= hv.trans h₂
   obtain ⟨p,hp',H⟩:= punctum Q o S V b' b g hp E Y e hs (by omega)
   obtain ⟨Z₁,Z₂,Z₃,hZ₁,hZ₂,hZ₃,P⟩:= lampL S.L (l+1+2) N F' a d A B r D hp (parksX V E b hp Z).ruled hx hy hθ hr he' hκ (by omega) (k:=k)
   have ht :=litE S ‹Teller su› V E b Z _ Z₁ g Z₂ Z₃ (Sienna.posts S.L S Q.table b V E hp).1 Q.table_exists hp hZ₁ hZ₂ hZ₃ (show 0< θ*2 by positivity) h₁ h₂ h₃ hM hp' N -- _ P
   filter_upwards [H,P,ht,cons Q.table_exists V E b g Z ξ,Delay.shift_pos su S.L] with x ht hp hh hk hx c f G h I F T he hv β R R' hX hy₁ hv₁ hQ hA' hW' ht' hr' ρ he₀ hV i Q' y h hΩ hz hZ hk' W hv' hR J U θ' hP hW m hS E' X
   have hF:0<furl su S.L x:=Real.rpow_pos_of_pos hx _; have hX':= ht _ _ _ _ _ he hv hQ hy₁ hv₁ hW' _ ht' ρ he₀ hV i Q' h hΩ hZ R R' _ _ hz hr' hk' W hv' ((le_add_of_nonneg_right hF.le).trans_lt hR)
   have hϘ:= hk c f I F T i he hv hQ hy₁ hA' ρ he₀; have hu₁:= (hϘ.curve 0 (by rw [norm_zero]; exact hϘ.pos)).nonneg
   obtain ⟨hu',hv',ht''⟩:=hp c f G _ _ _ _ hQ hX J U θ' hP hW m hS hu₁
   exact hh c f I F T i he hv hy₁ R β hQ hA' ρ he₀ hz.laws.intake _ ht'' (hu'.comp F.continuous_drape) (fun i=>hv' _) _ hX' hR
end coast
end YM.QCD.Octave
#print axioms YM.QCD.Octave.verdant
