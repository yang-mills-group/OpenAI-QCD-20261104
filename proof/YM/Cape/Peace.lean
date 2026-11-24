import YM.Hypnos.Cirque
set_option autoImplicit false
noncomputable section
namespace YM.Hypnos
open Filter Function Lattice Wilson Tree RG Pressure Finset MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations Push.SectorMeasure Push.SectorMeasure.Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Coat Blaze.Vine
open Shell Channel

open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Next.SectorChange
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Matrix Census Green Mask Pulse Itinerary Matter Poll Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{β τ C μ W:ℝ} {o: ConnectedActivityE6.Target.Order G W}{Q:ConnectedActivityE6.Target G P} {X:S.Choices} {r u t d A M D:ℝ}{F:Tree.Forest S.ratio}{n:ℕ}

lemma relaxP (Y:Coat T F)(hv: Photic Y u t C 2)(h:d≤u)(ht:0≤t):Photic Y d t C 2:=⟨hv.light.relax h le_rfl ht,fun i hi=> hv.studies i (hi.trans h),fun i j k hi=> hv.horizon i j k (hi.trans h),fun i j k hi=>hv.peak i j k (hi.trans h),hv.shade⟩
lemma comfort (Y:Coat T F)(W:Support c)(b:Directions G c)(z:Air f G)(h:HaloV Y W β u d b z)(he:u≤A)(hc:d≤D): HaloV Y W β A D b z:=by obtain ⟨v,hb,h,hc'⟩:= h.chosen; exact ⟨v,hb.trans he,h,hc'.trans hc⟩
-- once the purchase holds, choose v actual parent point.
def ShelterP (W μ x A r C D :ℝ)(G:Gauge)(P:Teller G)(o:ConnectedActivityE6.Target.Order G W) (Q:ConnectedActivityE6.Target G P)(L:Side)(Pi₀:Patch):=∀ (c f:Side)(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), S.patch=Pi₀ → Target.GrantBodies W x μ L Q o A T → Stamp T → ∀ (Z:Coat T F), Z.x=x → Z.width=o.K→Z.manifest→∀ (Y:Support c)(b:Directions G c), ‖b‖ ≤ r →Z.V=increment 1 b → (∀ i∈Y,¬Inside i Z.seeds (30*Z.B))→ ∀ (R: Rep G f), Intake P T x R →∀ z:Air f G, Calm Z Y o.ξ R.beta z→HaloV Z Y R.beta (C*(Z.t+‖b‖)) D b z
-- extend.Profile halo for r.V.At.S.M. Note D may vary; can pay Rate.β.
lemma georgic (G:Gauge)(P:Teller G)(o:Target.Order G W)(Q:ConnectedActivityE6.Target G P)(Pi₀:Patch)(L:Side)(V:ℝ→ℝ)(hD:Pi₀.Branches P.bind G)(hV:Rate G L (-(1/2)) V)(hp:∀ᶠ x in atTop,0≤V x) (μ A:ℝ):∃ C:ℝ,∃ D:ℝ→ℝ,Rate G L (-1) D ∧ ∀ᶠ x:ℝ in atTop,ShelterP W μ x A (V x) C (D x) G P o Q L Pi₀:=by
    obtain ⟨r,Z,hr,hZ,h⟩:= JointLoad.Heir.orchestra G Pi₀ P hD 2 le_rfl
    obtain ⟨t,C,ht,hC,hM⟩:= Malachite.treasure G P L Pi₀ hD 2 le_rfl hV hp (-(1/2))
    obtain ⟨M,hH,hm⟩:= budget_expandBare G
    let s x:= M*(C x*(t x+V x)*V x); let v x:=V x+(fiery G x L+s x); let d x:=Z*v x; let U x:= Z*(temp x+v x)*v x+s x
    have hw:Rate G L (-1) s:=by convert (((hC.mul (ht.add hV)).mul hV).mul_left M) using 1; norm_num
    have hv:Rate G L (-(1/2)) v:= hV.add (Rate.flame.add (hw.weaken (by norm_num)))
    have hu: Rate G L (-1) U:=by refine Rate.add ?_ hw; convert ((((vein_temp G L).add hv).mul_left Z).mul hv) using 1; norm_num
    have ht': Rate G L (-(1/2)) (fun x=> M*(C x*(t x+V x))):=by convert ((hC.mul (ht.add hV)).mul_left M) using 1; norm_num
    refine ⟨2*Z,U,hu,?_⟩
    filter_upwards [h,hM,hp,hv.below (by norm_num) _ hr, ht'.below (by norm_num) 1 zero_lt_one] with x hx hy hV hv hb c f S T F hh hT hS Ω hΩ hU hP Y b hb' hk hI R he z hg; subst x
    let q:=Ω.x
    obtain ⟨h₁,h₂,h₃⟩:=hy _ _ S T hh hT.funds F Ω rfl
    let m:=M*(C q*(t q+‖b‖)*‖b‖); let f:=‖b‖+(Ω.t+m)
    have hm' :0 ≤ M:= by linarith
    have hs : m ≤ s q:=by unfold s m q; gcongr
    have hv': f ≤ v q:=by unfold v q; rw [← hT.funds.length_eq]; exact add_le_add hb' (add_le_add_right hs Ω.t) -- ingredient U= X.t
    have hy0:f ≤ r :=hv'.trans ((le_abs_self _).trans hv)
    have hf := fought Ω Y hT hU hP hg he.positive b le_rfl (relaxP _ h₃ hb' h₁) (hm S F Ω.x) (hx S T hh (booths hS hT.funds.funds) hT.room.buys F Ω.k) hy0 hI hk
    apply comfort _ _ _ _ hf
    · have h: M*(C q*(t q+‖b‖)) ≤ 1:=by
          apply le_trans _ ((le_abs_self _).trans hb); unfold q; gcongr
      have h₀: m≤ ‖b‖:=by unfold m; rw [← mul_assoc]; exact mul_le_of_le_one_left (norm_nonneg _) h
      change Z*f ≤ _; apply le_trans (b:= Z*(‖b‖+(Ω.t+‖b‖))) (mul_le_mul_of_nonneg_left (add_le_add_right (by exact add_le_add_right h₀ _) _) (by linarith)); nlinarith only [mul_pos (zero_lt_one.trans_le hZ) (show 0<Ω.t from hT.room.fiery)]
    · change Z*(temp q+f)*f+m≤U q; unfold U; refine add_le_add ?_ hs
      have hp:0 ≤temp q:= Work.E04.temp_nonneg _; have hm:0 ≤f:=by
            unfold f m; have hg:0 ≤ Ω.t:= hT.room.fiery.le; exact add_nonneg (norm_nonneg b) (add_nonneg hg (mul_nonneg hm' (mul_nonneg (mul_nonneg h₂ (add_nonneg h₁ (norm_nonneg b))) (norm_nonneg b))))
      gcongr; exact mul_nonneg (zero_le_one.trans hZ) (add_nonneg hp (hm.trans hv'))
end YM.Hypnos
#print axioms YM.Hypnos.georgic
