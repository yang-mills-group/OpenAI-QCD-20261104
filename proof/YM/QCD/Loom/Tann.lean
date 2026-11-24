import YM.QCD.Loom.Skein
/-! # Varn at the quiet walk margin -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Jets.Sun Bay Pine
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R :Rep su f}
variable {H:Cash W τ μ L Q o C T R}{ι D E K:Type}{N:ℕ}
local notation "M"=> radiusB τ
-- replace Bench travel by bounded memory.
lemma purseJ (F B:ℕ)(K d V p θ β D Z:ℝ)(L:Side){f:ℝ→ℝ}(h:Rate su L (-(1/2)) f)(hp:0<p)(ht:0<θ):∀ᶠ x in atTop,
   let q:= Z/(coneK L θ x/2)*f x
   let a:= (2*(radiusB x:ℝ)+1)^4*(D*wink L x)+(Real.exp (-p *fossil (radiusB x) B)+(coneK L θ x/2)⁻¹*f x)*V
   F*(AtomF.rays*q) ≤ coreRate L x ∧ highW L K β x^2*fingers F^2*(2*a) ≤ coreRate L x ∧ f x<coneK L θ x/2:=by
    have hu : Rate su L (-7/16) (fun x=> F*(AtomF.rays*(Z/(coneK L θ x/2)*f x))):=by
       simp_rw [div_eq_mul_inv Z]; exact ((((shade_e L ht.ne'|>.mul_left Z).mul h).mul_left _).mul_left _).weaken (by norm_num)
    let a x:= (2*(radiusB x:ℝ)+1)^4*(D*wink L x)+(Real.exp (-p *fossil (radiusB x) B)+(coneK L θ x/2)⁻¹*f x)*V
    have he : Rate su L (-7/16) a:=by
       unfold a; apply Rate.add; exact ((((Rate.radius_price.mul_left 2).add (Rate.const 1)).pow 4).mul (Rate.power.mul_left _)).weaken (by norm_num)
       have hp': Rate su L (-7/16) (fun x=> Real.exp (-p *fossil (radiusB x) B)):=by simpa only [sub_zero] using pale p 0 hp B
       exact (hp'.add (((shade_e L ht.ne').mul h).weaken (by norm_num))).mul_right _
    have hR:=((Rate.mul_right (Rate.pow ((Rate.rpow_monitor (G:=su) (L:=L) β).mul_left K) 2) (fingers F^2)).mul (he.mul_left 2))
    filter_upwards [hu (-(2/5)) (by norm_num),hR (-(2/5)) (by norm_num), (h.mul (shade_e L ht.ne')).below (by norm_num) (1/2) (by norm_num),kentucky L ht] with x hu he hx H
    dsimp only; have hw: 0<coneK L θ x/2:=half_pos (mul_pos ht (pow_pos H.1 _)); refine ⟨(le_abs_self _).trans hu,(le_abs_self _).trans he,(div_lt_one hw).mp ?_⟩
    rw [div_eq_mul_inv]; exact ((le_abs_self _).trans hx).trans_lt (by norm_num)
variable {j k:ℕ}
lemma insoleP (P: Plan j)(P': Teller su)(L:Side)(p' K θ D γ t a C g r θ':ℝ)(B i N:ℕ) (a' b' A' C' a₁ a₂:ℝ)(J:Plan k) {x:ℝ→ℝ}(hx:Rate su L (-(1/2)) x)(h:a>0)(ht:0 < t)(hh:0 < θ)(hK:0<K):∀ᶠ z in atTop,
    ∀ (c f :Side)(G:Flight j k)(e:f.val=c.val*G.L.val), G.L=L→∀ (O:Garden.Offer 1 a' A')(I: Garden.Offer 2 b' C')(m:ℝ), |m| ≤wink L z →
      let d:=sliceL G e; let s:=coneK L θ z; let Z:= park G e P O I (haloK L z) m
      Species G e r C s t a₁ B Z→∀ W:ℕ→Atom su 2, ∀ U:Swathe G e Z W J r s t p' D i, ∀ (F:StepData c f)(V:Tube su F)(X:Tree.Forest F.ratio)(Y:Coat V X),F.patch.L=L → Room P' F V z→ F.ratio=d→ Y.x=z → Y.manifest →Woods P' L a x z →∀ y:Varn f c,waxV y=none→∀ (v:Directions su f) (Z:Support c),
      let o:=F.ratio.parent (orbitM d y)
      halo (6*radiusB z) {o}⊆Z→ Y.enforce (2*a) v (Y.plaza Z)≠0 → ¬Inside o Y.seeds (18*radiusB z) → load (fun _=>highW L K γ z) (Cove.light _ (Port.sliceF U N (radiusB z) y (Y.input v))) ≤ coreRate L z:=by
    obtain ⟨d,hD,hp⟩:= Fork.halo_chart
    filter_upwards [Delay.shift_pos su L,kentucky L hh,purseJ N i K d p' t θ γ (foamD L P a₁) D L (hx.mul_left d) ht hh] with z he hz ht' c f G eg hL O I m hm r' s Z hZ W U F V X Y hv hF hr hX hY HP y hy u Q o hQ hf hB
    obtain ⟨p,b,hb⟩:=HP.cloth Y hX hv hF hY Q o u hQ hf hB
    have hv': 0<s :=mul_pos hh (pow_pos hz.1 _); let a'':= highW L K γ z; have hκ:0<a'':=mul_pos hK (fan_pos ..) -- issue dependency, need convert hb before
    have he:= weir Y u (orbitM (sliceL G eg) y) p b hF.sight.1 HP.frames hD.le hp (show Blanket F (Y.input u) Y.V _ _ p b _ from hb)
    rcases y with ⟨k'',l⟩|⟨k'',l⟩ <;> change l=none at hy <;> subst l
    · exact le_trans (scalar_trim U N (radiusB z) _ k'' _ hv' he ht'.2.2 ht.le) ht'.1
    have hξ : ‖Port.dusk G eg J Z 1‖ ≤ foamD L P a₁*wink L z:=by
      apply le_trans (unspent hZ); rw [hL]; unfold foamD; have hv:= hZ.calf; have he:= mass_pos L; have hg:= healthy P L
      exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hg.le) (by positivity)) he.le) he.le) (le_of_eq (by ring))
    have he':= crop_p U N (radiusB z) (Y.input u) k'' _ hv' he ht'.2.2 ht.le hξ; have hg:= farm_price U N (radiusB z) k'' (Y.input u) none hv' hκ _ _ (fun _=>le_rfl) (fun _=>le_rfl)
    apply le_trans hg; apply le_trans _ ht'.2.1; rw [two_mul]; exact mul_le_mul_of_nonneg_left (add_le_add he'.1 he'.2) (by positivity)
end YM.QCD.Loom
