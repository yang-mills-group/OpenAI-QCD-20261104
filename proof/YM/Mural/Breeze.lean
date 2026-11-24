import YM.Mural.Arch
/-! # sale of global wood veneers -/
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
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R :Rep su f}
variable {H:Cash W τ μ L Q o C T R}{N m l n:ℕ}
variable {X:Run.St c}{Γ:Land c (Site c) (Site c)}{Y:Pays c (Site c) (Site c)} {η p d a θ:ℝ}

open MassiveQCD.Apron

set_option maxHeartbeats 510000 in
lemma garrison {p θ K x :ℝ}(hw: 0≤x)(hu: p>d)(h:0<θ)(hh: θ<1/8)(hX:1≤K)(L: Side) (j b':ℕ)(hv:0<η)(hP:0 ≤ b){m':ℝ→ℝ}(hK:Rate su L (-(1/2)) m') (P:Teller su)(Q:ConnectedActivityE6.Target su P) (W:ℝ)(H:Target.Order su W) (a:ℝ)
    (hc:0≤d) (hp: reserve d Q.relative (10* preCost 37) 1): ∀ᶠ z in atTop,
    let B:=radiusB z; let v:=highW L K θ z; let Z:=coreRate L z
    ∀ (c f : Side)(S: StepData c f)(T : Tube su S)(R:Rep su f), S.patch.L=L→∀ (O:Tree.Forest S.ratio)(g : Run.St c) (Y:Land c (Site c) (Site c))(P':Pays c (Site c) (Site c)),Pack id id η p b' g b Y P'→∀ (X :Cash W z a L Q H x T R), Woods P L H.a m' z→ let w i:= Real.exp 1*glaze P' Z v j B i; Stern (sailP X Y j) O univ Prod.fst (glaze P' Z v j B) v (fan L (1/4) z) (univ.filter fun i=> i.2 = none) (18*B) 1 (fun i U V=>dropG j Y S.ratio B i U V) ∧ Ac.Hit (sailP X Y j).ground B w Q.relative (betaF su z L ^(-(3/8):ℝ)):=by
   let K' z:=coreRate L z* Real.exp d+utt b (radiusB z) b' p d j (highW L K θ z)
   have hL: Rate su L (-(2/5)) K' := by
      apply Rate.add (Rate.power.mul_right (Real.exp d)); unfold utt
      have hx:Rate su L (-(2/5)) (fun i=> Real.exp (-(p-d)*fossil (radiusB i) b')) := Touch.pale p d hu _
      exact ((((Rate.rpow_monitor (G:=su) (L:=L) θ).mul_left K|>.pow 2).mul_right _).mul (hx.mul_right b |>.mul_left 4)).weaken (by linarith)
   let T' z:= rem 1 37 (radiusB z) Q.relative (K' z) 1
   have hg : Seat L 0 (fun i=> Jets.Sun.rem 1 37 (radiusB i) Q.relative 1 1):=by
      unfold rem Footprint.payment degreeIncome; simp only [Footprint.spread,extentCost,Nat.cast_mul]; exact ((expensed (L:=L) 0 (37+20) 0).timesL _|>.timesL _|>.times _|>.times _)
   have hp' : Rate su L (-(2/5)) T' := by unfold T'; simp_rw [leeway 1 (K' _)]; exact (hg.ruled.mul hL).weaken (by linarith)
   obtain ⟨r,hr,Y⟩:=Fork.halo_chart
   let v z:=highW L K θ z
   let ξ z:=r*((L.val:ℝ)*m' z); have hξ:= (hK.mul_left (L.val:ℝ)).mul_left r
   have hW : Rate su L (-(1/2)) (fun z=> v z^2*fingers j^2*(4*ξ z/(η/2)*b)):=by
      have he:=(((Rate.rpow_monitor (G:=su) (L:=L) θ).mul_left K).pow 2|>.mul_right (fingers j^2))
      simp_rw [div_eq_mul_inv ((4:ℝ)*_)]; exact (he.mul ((((show Rate su L _ _ from hξ).mul_left _).mul_right _).mul_right _)).weaken (by linarith)
   filter_upwards [hL.below (by norm_num) 1 one_pos,hξ.below (by norm_num) (η/3) (by positivity), hW (-(2/5)) (by norm_num), (hp'.mul_left (Real.exp 1)) (-(3/8)) (by norm_num),Work.E01.radiusB_tendsto.eventually_ge_atTop (L.val+b'+1), Port.crop_cost L j 0 (b+b) K K h hh,Delay.shift_pos su L] with z hu' hy hU hp' hZ hc' hz B v Z c f S T R hP' O g Y₀ P' hR X HX w
   let p':= glaze P' Z v j B; have hZ':0<Z:=Real.rpow_pos_of_pos hz _; have hc₀:0<K:=zero_lt_one.trans_le hX; have hv':0<v:=mul_pos hc₀ (fan_pos ..)
   have hℓ(i): 0≤p' i:=by unfold p' glaze; split; exact hZ'.le; exact galaN hR ..
   have hF (i):0≤w i:=mul_nonneg (Real.exp_pos _).le (hℓ i)
   let I:=sailP X Y₀ j
   have hs : S.ratio.count.val+1 ≤ B:=by rw [show S.ratio.count=L from hP']; unfold B; omega
   have hf:b'≤B:=by unfold B; omega
   have hB:= fleets hR _ j B v hZ'.le hf hu.le hc
   have hT i : p' i≤1:= (anchored_each _ p' _ hB hc hℓ i).trans ((le_abs_self _).trans hu')
   have hM :0<B:=by omega
   constructor
   · refine ⟨fun x U V=>rfl,fun x U V=>kid _, galeCase X O hP' g Y₀ P' j b' z rfl v Z hv' hZ' hu hc hv hR hs hf hT m' HX r hr Y hy hU hc',hℓ,?_⟩ -- frame packing
     intro i Z₁ hu₁ h₂ hv₁ q h1 hx
     have ht' : i.2=none:=by
        by_contra hn; apply not_lt_of_ge _ hx; rw [glaze,if_neg hn]; exact galaP (X:=g) hR i B j _ _ hv hv'
     rcases i with ⟨k,l⟩; change l=none at ht'; subst l; let i:Gaze c:=(k,none); have hJ:p' i=Z:=if_pos rfl
     refine ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,?_⟩
     have hI:Inside k Z₁.seeds (18*B) :=by
        by_contra hI
        let V:=plank (sashP i B) S.ratio B; let U:=Z₁.liftA R.beta q
        have hm: Z₁.enforce (2*H.a) U (Z₁.plaza V)≠0:= h1
        have hQ := X.laws.data
        obtain ⟨G,Gg,hG⟩:= HX.cloth Z₁ hu₁ hP' hQ.room hv₁ V k U (seaP i B _) hm hI
        have hh₁: S.ratio.count.val=L.val:=by rw [show S.ratio.count=L from hP']
        have hv : ‖token c j v (dropG j Y₀ S.ratio B (k,none) (Z₁.input U) Z₁.V)‖ ≤ Z:=by
           have hh := galaSky hR k (4*B) j B Z₁ U _ G Gg r hv' (hc.trans hu.le) hv hG hr.le Y HX.frames (by rw [hh₁]; apply lt_of_le_of_lt ((le_abs_self _).trans hy); linarith) (by have Bv:B=radiusB z:=rfl; omega)
           refine hh.trans ?_; rw [hh₁]; exact (le_abs_self _).trans hU
        exact not_lt_of_ge hv (hJ ▸ hx)
     obtain ⟨x,hx,hk⟩:= halo_spec.mp hI; exact ⟨x,halo_spec.mpr ⟨k,seaP i B _ (halo_subset _ _ (mem_singleton_self _)),(separation_comm ..).trans_le (hk.trans (by change 18*B ≤30*B; omega))⟩,hx,hk⟩

   have hπ:Ac.Hit I.ground B p' Q.relative (T' z):= gameP X g Y₀ j B rfl (K' z) p' hs hM hB hp hℓ
   have hu : Ac.Hit I.ground B w Q.relative (Real.exp 1*T' z):= heights_factor (Real.exp 1) _ _ _ hπ (fun _=> rfl) (Real.exp_pos _).le
   exact fun i=> budget_loosen (hu i) ((le_abs_self _).trans hp')
end YM.QCD.Loom

#print axioms YM.QCD.Loom.garrison
