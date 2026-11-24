import YM.Poised.Rally
import YM.Poised.Caliph
import YM.Poised.Strand
/-! # payouts before L and post.M. no origin requirement used on invoice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG MassiveQCD.Plate MassiveQCD.Apron MassiveQCD.Elevator
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open QCD.Dust QCD.Brick Pipes Spice MassiveQCD.Lyre Shells Sands MultiNext.SignedSource.Ease
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ σ η μ W:ℝ}
variable {R Rx:Rep su f}{O O₁:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {δ y h t u :ℝ}{q p n m j k α:ℕ}
namespace TrainG
open Steed Chute Planned.PrimaryIntegral295.Carrier
lemma gold (j k:ℕ)(K:KernelChoices)(L:Side)(hp:4≤j)(hk:4≤k): ∃ σ A:ℝ, 0<σ ∧ 0≤ A ∧ ∀ (P:Flight j k),P.L=L→(linesOf P K.penalty).strip σ A ∧∀ i j:Pipes.Shell,∀ x:Cover,Width σ A (arch P i j x):=by
    obtain ⟨a,b,ha,hb,H⟩:= priced K.penalty K.penalty_pos hp hk; obtain ⟨c,d,hc,hd,h⟩:= archY hk L hp
    refine ⟨min c a,max d b,lt_min hc ha,hd.trans (le_max_left ..),fun P hP=>?_⟩; obtain hE:=H P [] (by simp); unfold advanceC at hE
    refine ⟨fun i j=>(hE i j).mono (min_le_right c a) (le_trans ?_ (le_max_right ..)),fun i j x=> (h P hP i j x).mono (min_le_left ..) (le_max_left ..)⟩
    exact div_le_self hb.le (one_le_pow₀ (Nat.one_le_cast.mpr P.L.property))
abbrev sector (p n:ℕ)(L:Side)(x:ℝ):ℕ:= radiusB x*p+n
abbrev voyage (p:ℕ)(q0 r:ℕ):ℕ:=4*(q0*(4*r+2)+2*r)+p
lemma nova (u:ℕ)(a:ℝ→ℕ)(L:Side)(h:Seat L 0 (fun x=>(a x:ℝ))): Seat L 0 (fun x=>(↑(voyage u (a x) (2*radiusB x)):ℝ)):=by
    have hg:=Jets.Touch.Seat.radius (L:=L)
    unfold voyage; push_cast; apply Seat.comb _ (Seat.numbers (↑u:ℝ)); apply Seat.timesL
    refine Seat.comb (by simpa only [zero_add] using (h.ponies (((hg.timesL 2).timesL 4).comb (Seat.numbers 2)))) ((hg.timesL 2).timesL 2)
lemma herring {A:ℝ→ℕ} (h:Seat L 0 (fun x=>(A x:ℝ))) (p n:ℕ) : Seat L 0 (fun x=> ratioP p n (A x)):=by
    unfold ratioP pups; simpa only [zero_mul] using (((Seat.numbers 1|>.comb h).powered (p*p)).powered n)
lemma sunset (L:Side)(hσ:0 < σ)(a:ℝ):Seat L a fun x=> tar σ (radiusB x):= by
    have he : Rate su L (-1) (fun x=>Real.exp (-(σ/2)*radiusB x)):=by
       refine (Rate.cutoff (G:=su) (L:=L) (a:=-1) (half_pos hσ)).compare (Eventually.of_forall fun x=>?_)
       rw [abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (Real.exp_nonneg _),Real.exp_le_exp]; exact mul_le_mul_of_nonpos_left (show (Pressure.Stores.till x:ℝ)≤radiusB x from Nat.cast_le.mpr (Nat.div_le_self ..)) (neg_nonpos.mpr (half_pos hσ).le)
    exact Seat.timesL (Seat.eliminated he (by norm_num)) _ -- inferred σ etc
-- L⁻¹ per polynomial exponent budget.Meet.Pims at specified power.Order Merit.
lemma badge_pay (p g q:ℕ)(C : Libretto su n)(t:ℝ)(ht:0<t):∃ M:ℝ,0≤ M ∧ ∀ (b v:ℕ)(B:BudgetPoint), B.power=p→ b≤ v*9^4 → badgeQ C B g b ≤ M*Real.exp (t*v):=by
   let k:=Lute.debited n p; let p':ℝ:=9^4; let m n:=(1+(n:ℝ))^k; let D:=Hera.ripple C 1; let X(v:ℕ):=1+(v:ℝ); let K:=k+3*g
   let M:= 1+2*D*p'^k
   have hD:0≤ D:=by unfold D Hera.ripple; positivity [Lute.leading_one C]
   have h1:0≤p':=by unfold p'; positivity
   have hM :1 ≤ M:=by unfold M; exact le_add_of_nonneg_right (by positivity) -- 1+_ >... replace
   let Z:=M*p'^(3*g)
   refine ⟨Z*ChargeF t K,by unfold Z ChargeF; positivity,fun b v B hB he=>?_⟩
   have ht' :X b ≤ p'*X v:=by
     have hm:(b:ℝ)≤v*(9:ℝ)^4:=by exact_mod_cast he
     unfold X p'; linarith
   have ha:1≤X v:= by simp [X]
   have h:1≤X b:=by simp [X]
   have hz : 1+Hera.dueFee C B b ≤ M*X v^k:=by
       let S:= (1+(b:ℝ)); have hb:1≤ X v^k:=one_le_pow₀ ha; have hq':X b^k≤p'^k*X v^k:= (pow_le_pow_left₀ (zero_le_one.trans h) ht' k).trans_eq (mul_pow ..); unfold Hera.dueFee; rw [hB]; unfold M; change 1+D*(1+X b^k)≤ _; nlinarith only [hb, mul_le_mul_of_nonneg_left hq' hD,mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=k) h) hD]
   apply (mul_le_mul hz ((pow_le_pow_left₀ (zero_le_one.trans h) ht' (3*g)).trans_eq (mul_pow ..)) (pow_nonneg (zero_le_one.trans h) _) (by positivity)).trans
   calc _= Z*X v^K:=by unfold Z K; rw [pow_add]; ring
        _≤ Z*ChargeF t K*Real.exp (t*v):=by rw [mul_assoc Z]; exact mul_le_mul_of_nonneg_left (polynomial_cost ht (Nat.cast_nonneg v) K) (by unfold Z; positivity)
lemma beyond (P':Libretto su n)(i p k:ℕ)(t u:ℝ)(ht:0<t)(ha:0≤u): ∃ L':ℕ,∃ A:ℝ, 1≤A ∧ ∀ (L:Side), L' ≤ L.val →∀ (B:BudgetPoint), B.power=p → ∀ (c f:Side)(S:Ratio c f),S.count=L →∀ (s s₀ s':ℕ),s≤ s₀*9^4 → (s':ℝ)≤ preCost k+conversion S k*s₀ →
     Real.exp (u*s') * badgeQ P' B i s ≤ A*Real.exp (t*s₀):=by
    let b:=t/4; have hb:0<b:=by unfold b; positivity
    obtain ⟨A,hA,H⟩:=badge_pay p i 0 P' b hb; obtain ⟨z,hz⟩:=Fees.exponent k hb ha (show 2*b<t from by unfold b; linarith)
    let M:=A* Real.exp (u*preCost k); refine ⟨z,1+M,by unfold M; linarith only [show 0≤A*Real.exp (u*preCost k) by positivity],?_⟩; intro L hL B hB c f S h s s₀ s' h' hS
    have He:= hz c f S (h.symm ▸ hL); let e:=Real.exp (t*s₀); have h2 :Real.exp (u*s')* Real.exp (b*s₀)≤Real.exp (u*preCost k)*e:=by rw [← Real.exp_add]; unfold e; rw [←Real.exp_add]; apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_left hS ha, mul_le_mul_of_nonneg_right He.2.2 (Nat.cast_nonneg (α:=ℝ) s₀), mul_nonneg hb.le (Nat.cast_nonneg (α:=ℝ) s₀)] -- might need multiplication by s₀
    exact (mul_le_mul_of_nonneg_left (H _ _ _ hB h') (Real.exp_pos _).le).trans (le_trans (le_trans (le_of_eq (by rw [mul_left_comm])) ((mul_le_mul_of_nonneg_left h2 hA).trans_eq (mul_assoc ..).symm)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (Real.exp_pos _).le)) -- specificity
end TrainG
end YM.Massive.Poised
#print axioms YM.Massive.Poised.TrainG.beyond
