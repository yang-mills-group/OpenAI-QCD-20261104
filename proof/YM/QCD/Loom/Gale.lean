import YM.QCD.Loom.Home
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
-- price formula weighted Halo B masks, rig mandatory. Buy via ratio id. awards cap. Invariant periodic Fare perk separately.
def glaze (Y:Pays c (Site c) (Site c))(Z a:ℝ)(N B:ℕ)(i:Gaze c):ℝ:= if i.2=none then Z else gala Y i B N a
def utt (b:ℝ)(B m:ℕ)(p d:ℝ)(N:ℕ)(a:ℝ):= a^2*fingers N^2*(4*(Real.exp (-(p-d)*fossil B m)*b))
lemma fleets (hx : Pack id id η p n X b Γ Y) (Z:ℝ) (N B:ℕ)(a:ℝ)(he:0≤Z)(ht:n ≤ B)(hp:p≥d)(hw:0≤d): Anchored Prod.fst (glaze Y Z a N B) (fun i=>coverNumber B (sashP i B)) d (Z*Real.exp d+utt b B n p d N a):=by
   intro i; let E:=glaze Y Z a N B; have hv j:0≤E j:=by unfold E glaze; split; exact he; exact galaN hx ..
   refine ⟨fun j=> ?_,Summable.of_finite,?_⟩
   · dsimp only; split; exact mul_nonneg (hv _) (Real.exp_pos _).le; exact le_rfl
   let G z:= (glaze Y Z a N B (i,z))*Run.rent d B (punch i B z)
   rw [tsum_fintype,Fintype.sum_prod_type]; rw [sum_eq_single i]; rotate_left
   · intro b _ hb; exact sum_eq_zero fun j _=> if_neg hb
   · simp
   change (∑ j:XMark c, if i=i then G j else 0) ≤ _ -- defeq
   simp only [if_true]; rw [Fintype.sum_option]; apply add_le_add
   · rw [show G none=Z*Run.rent d B (punch i B none) from ?_] -- edit
     · exact mul_le_mul_of_nonneg_left (one_more i B hw) he
     simp [G,glaze]
   let P(x y:Site c)(V:Support c):=crease i B Y x y (some V)*Run.rent d n (punch i B (some V))
   have h p': G (some p') ≤ gala Y (i,some p') B N a*Run.rent d n (punch i B (some p')):= by
      unfold G glaze; rw [if_neg (by simp)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (YM.Next.Scheduling.cover_earns ht _)) hw)) (galaN hx ..)
   apply (sum_le_sum (fun p _=> h p)).trans; simp only [gala,mul_assoc (a^2*fingers N^2), Finset.sum_mul]
   rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ (by positivity); simp_rw [add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum] -- edits term
   let V:= Real.exp (-(p-d)*fossil B n)
   have ht : (∑ U:Support c,∑ j,P i j U)≤V*b:=by rw [Finset.sum_comm]; apply (sum_le_sum (fun j _=> Port.cash_l hx i j i B (Or.inl rfl) hp)).trans; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hx.spends i) (Real.exp_pos _).le
   have he' : (∑ U:Support c,∑ j,P j i U)≤V*b:=by rw [Finset.sum_comm]; apply (sum_le_sum (fun j _=> Port.cash_l hx j i i B (Or.inr rfl) hp)).trans; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hx.dues i) (Real.exp_pos _).le
   change 2*(∑ U:Support c,∑ j,P i j U)+2*(∑ U:Support c,∑ j,P j i U) ≤4*(V*b); linarith
set_option maxHeartbeats 300000 in
lemma galeCase (X:Cash W τ μ L Q o C T R) (O: Tree.Forest S.ratio)(hP':S.patch.L=L)(g:St c)(Y₀:Land c (Site c) (Site c))(P':Pays c (Site c) (Site c))(j b':ℕ)(z:ℝ)(hz:z=τ)(v Z:ℝ)(hv':0<v)(hZ':0<Z)(hu: p>d)(hc:0≤d)(hv:0<η)(hR:Pack id id η p b' g b Y₀ P') (hs : S.ratio.count.val+1 ≤radiusB z)(hf:b' ≤radiusB z)(hT:∀ i,glaze P' Z v j (radiusB z) i≤1) (m':ℝ→ℝ)(HX : Woods P L o.a m' z)(r:ℝ)(hr:0<r)(Y:∀ i, ‖colour i-1‖ ≤r*su.chord i)(hy:|r*(L.val*m' z)| ≤η/3)(hU:|v^2*fingers j^2*(4*(r*(L.val*m' z))/(η/2)*b)| ≤ Z)(hc' : Real.exp (max (↑j*AtomF.rays*2*0) (v^2*fingers j^2*(2*(b+b)))) ≤ wear L z*(Real.exp 1* Z)) :
   let w i:=Real.exp 1*glaze P' Z v j (radiusB z) i; Fleet.Theft (sailP X Y₀ j) O Prod.fst w v (fan L (1/4) z) (univ.filter fun i=> i.2 = none) (18*(radiusB z)) 1:=by
   subst τ; intro w; let B:=radiusB z; let p':= glaze P' Z v j B; change ∀ i,p' i≤1 at hT; change S.ratio.count.val+1 ≤ B at hs
   have hℓ(i): 0≤p' i:=by unfold p' glaze; split; exact hZ'.le; exact galaN hR ..
   have hF (i):0≤w i:=mul_nonneg (Real.exp_pos _).le (hℓ i)
   let I:=sailP X Y₀ j
   have hM :0<B:=by omega
   have hY Z i q : ‖token c j v (Fleet.coming (F:=O) I i Z q)‖ ≤ Real.exp (gala P' i B j v)-1:=by
     apply (I.riseTiny Z q _ i v).trans; exact Cove.bought (fun _=>v) _ _ (galaP (X:=g) hR i B j (Z.input (Z.liftA R.beta q)) Z.V hv hv')
   have he Z i q (hk : i.2 ≠ none): ‖token c j v (Fleet.coming (F:=O) I i Z q)‖ ≤w i:=by
       apply (hY Z i q).trans
       rw [← show p' i= _ from if_neg hk]; exact fastR _ (hℓ _) (hT _)
   have hi: 0<fan L (1/4) z:=fan_pos ..
   refine ⟨hi.le,hF, ?_,fun i Z₁ hu₁ h₂ hv₁ q hx=>?_,fun i Z ht hK hm v' => ?_⟩
   · intro x
     rw [Finset.card_le_one]; intro u hu v hv; simp only [mem_filter, mem_univ,true_and] at hu hv; exact Prod.ext (hu.2.trans hv.2.symm) (hu.1.trans hv.1.symm)
   · have ht': i.2=none:=by_contra (fun hi=>not_lt_of_ge (he _ _ _ hi) hx)
     rcases i with ⟨k,l⟩; change l=none at ht'; subst l; let i:Gaze c:=(k,none); have hJ:p' i=Z:=if_pos rfl
     refine ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,?_⟩
     have hI:Inside k Z₁.seeds (18*B) :=by
        by_contra hI
        let V:=plank (sashP i B) S.ratio B; let U:=Z₁.liftA R.beta q
        have hm: Z₁.enforce (2*o.a) U (Z₁.plaza V)≠0:=by
           change I.riseP Z₁ q i≠_; intro h; change w i < ‖token _ _ v (I.riseP Z₁ q i • _)‖ at hx; rw [h,zero_smul,map_zero,norm_zero] at hx; exact not_lt_of_ge (hF i) hx
        have hQ := X.laws.data
        obtain ⟨G,Gg,hG⟩:= HX.cloth Z₁ hu₁ hP' hQ.room hv₁ V k U (seaP i B _) hm hI
        have hh₁: S.ratio.count.val=L.val:=by rw [show S.ratio.count=L from hP']
        have hv : ‖token c j v (dropG j Y₀ S.ratio B (k,none) (Z₁.input U) Z₁.V)‖ ≤ Z:=by
           have hh := galaSky hR k (4*B) j B Z₁ U _ G Gg r hv' (hc.trans hu.le) hv hG hr.le Y HX.frames (by rw [hh₁]; apply lt_of_le_of_lt ((le_abs_self _).trans hy); linarith) (by omega)
           refine hh.trans ?_; rw [hh₁]; exact (le_abs_self _).trans hU
        apply not_lt_of_ge _ hx; apply (I.riseTiny Z₁ q _ (k,none) v).trans; exact (Cove.bought (fun _=>v) _ _ hv).trans (show Real.exp Z-1 ≤w i by rw [show w i=Real.exp 1*Z from congr_arg (Real.exp 1 * ·) hJ]; exact fastR _ hZ'.le (hJ ▸ hT i))
     obtain ⟨x,hx,hk⟩:= halo_spec.mp hI; exact ⟨x,halo_spec.mpr ⟨k,seaP i B _ (halo_subset _ _ (mem_singleton_self _)),(separation_comm ..).trans_le (hk.trans (by change 18*B ≤30*B; omega))⟩,hx,hk⟩
   · by_cases hi':i.2≠none
     · exact (he Z i v' hi').trans (le_mul_of_one_le_left (hF i) (Real.one_le_exp hi.le))
     push Not at hi'; rcases i with ⟨i,l⟩; change l=none at hi'; subst l; apply (hY Z (i,none) v').trans
     apply le_trans (sub_le_self _ zero_le_one); apply le_trans (Real.exp_monotone (galaSun hR i B j (hc.trans hu.le)))
     refine le_trans (Real.exp_monotone ((show v^2*fingers j^2*(4*b)= v^2*fingers j^2*(2*(b+b)) by ring).trans_le (le_max_right (↑j*AtomF.rays*2*0) ..))) ?_
     refine le_trans hc' (le_of_eq ?_); congr 1

set_option maxHeartbeats 350000 in
lemma gameP (X:Cash W τ μ L Q o C T R)(g:St c)(Y₀:Land c (Site c) (Site c))(j:ℕ)(B:ℕ)(hZ:B=radiusB τ)(b :ℝ)(p':Gaze c→ℝ)(hs:S.ratio.count.val + 1 ≤B)(hM:0<B)(hB: Anchored Prod.fst p' (fun i=>coverNumber B (sashP i B)) d b)(hp:reserve d Q.relative (10*preCost 37) 1) (hℓ:∀ i,0≤p' i): Ac.Hit (sailP X Y₀ j).ground B p' Q.relative (Jets.Sun.rem 1 37 B Q.relative b 1) := by
   subst B; let Z:=radiusB τ
   have ht:∀ i:Gaze c, (sailP X Y₀ j).ground i⊆enlargement (singleR c) 37 Z (sashP i Z):=fun i=>clover i Z S.ratio hs
   have hr: reserve d Q.relative (conversion (singleR c) 37) 1:= by simpa [conversion,singleR] using hp
   have he : Z ≤ 2*Z := by omega
   have hk:= Jets.Touch.offers Prod.fst _ _ (fun i=>Port.cared ..) ht hℓ hB hM he hr; rw [show (singleR c).count=1 from rfl] at hk; exact hk

set_option maxHeartbeats 400000 in
lemma forwardG {p θ K x :ℝ}(hw: 0≤x)(hu: p>d)(h:0<θ)(hh: θ<1/8)(hX:1≤K)(L: Side) (j b':ℕ)(hv:0<η)(hP:0 ≤ b){m':ℝ→ℝ}(hK:Rate su L (-(1/2)) m') (P:Teller su)(Q:ConnectedActivityE6.Target su P) (W:ℝ)(H:Target.Order su W) (a:ℝ)
    (hc:0≤d) (hp: reserve d Q.relative (10* preCost 37) 1): ∀ᶠ z in atTop,
    let B:=radiusB z; let v:=highW L K θ z; let Z:=coreRate L z
    ∀ (c f : Side)(S: StepData c f)(T : Tube su S)(R:Rep su f), S.patch.L=L→∀ (O:Tree.Forest S.ratio)(g : Run.St c) (Y:Land c (Site c) (Site c))(P':Pays c (Site c) (Site c)),Pack id id η p b' g b Y P'→∀ (X :Cash W z a L Q H x T R), Woods P L H.a m' z→ let w i:= Real.exp 1*glaze P' Z v j B i; Fleet.Theft (sailP X Y j) O Prod.fst w v (fan L (1/4) z) (univ.filter fun i=> i.2 = none) (18*B) 1 ∧ Ac.Hit (sailP X Y j).ground B w Q.relative (betaF su z L ^(-(3/8):ℝ)):=by
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
   refine ⟨galeCase X O hP' g Y₀ P' j b' z rfl v Z hv' hZ' hu hc hv hR hs hf hT m' HX r hr Y hy hU hc',?_⟩
   have hπ:Ac.Hit I.ground B p' Q.relative (T' z):= gameP X g Y₀ j B rfl (K' z) p' hs hM hB hp hℓ
   have hu : Ac.Hit I.ground B w Q.relative (Real.exp 1*T' z):= heights_factor (Real.exp 1) _ _ _ hπ (fun _=> rfl) (Real.exp_pos _).le
   exact fun i=> budget_loosen (hu i) ((le_abs_self _).trans hp')
end YM.QCD.Loom
