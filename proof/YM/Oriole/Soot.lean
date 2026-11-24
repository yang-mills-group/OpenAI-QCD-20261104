import YM.Oriole.Hoop
import YM.QCD.Entr.Stage
import YM.QCD.Entr.Penny
import YM.Massive.Mass.Kernels
/-! axis-one moment with tape (Anchor n ligand). Grants exact error on all orientations for wood.B. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr.Goals
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Eyrie Rudder Sparks Pearl YM.Next.Free Bloch Laurent
open Massive.SourceRead Massive.Oriole Massive.UV
variable (F:Taper)(X:Gleam)
open Globe
lemma N_one (i:Site c)(j:Axis): Nw F (first j) i= Np F i* (Lattice.lift i j:ℂ):=by
     unfold Nw Massive.SourceRead.profile; rw [one_pow,one_mul,prod_eq_single j]; rw [Massive.Oriole.nectar,if_pos rfl,pow_one,Nat.factorial_one]; simp
     intro k _ h; rw[Massive.Oriole.nectar,if_neg h.symm, pow_zero]; simp
     simp
lemma N_price (x:Site c)(j:Axis): ‖Nw F (first j) x‖ ≤ (pdist x:ℝ):=by rw [N_one,norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (tintE x F)).trans; rw[← Complex.ofReal_intCast, Complex.norm_real]; exact liftN x j
noncomputable def Rod (c:Side)(F:Taper)(t:Axis): Sheet c →ₗ[ℂ]Bundle:=
    let f(K:Sheet c):= ∑ p:Site c, Nw F (first t) p • Run.cell K 0 p; { toFun:=f, map_add':=fun X Y=>by unfold f; simp_rw [show ∀ i j:Site c,Run.cell (X+Y) i j=Run.cell X i j+Run.cell Y i j from fun i j=>rfl, smul_add, Finset.sum_add_distrib], map_smul':=fun z x=>by unfold f; simp_rw[Run.cell_scale, Finset.smul_sum]; refine sum_congr rfl fun i _=>smul_comm .. }
local notation "R"=> Rod c F 0
lemma learns (i:Axis)(M:Sheet c)(h:Globe.Beam M 1 a):‖Rod c F i M‖ ≤ a:=by -- Beam amb
     let B:=M; refine (norm_sum_le (s:= (univ:Finset (Site c))) _).trans ((sum_le_sum (fun p _=> ?_)).trans (h.toR (0:Site c))); rw [norm_smul]; apply mul_le_mul_of_nonneg_right (le_trans (N_price F p i) (by change _≤ costS 1 0 p; rw[costS,separation_comm 0 p,pow_one,separation,sub_zero]; linarith)) (norm_nonneg _) -- fix
noncomputable def Rv (F:Taper) (i:Axis): Sheet c→ₗ[ℂ] Bundle:=
    let f(K: Sheet c):= ∑ p:Site c,Nw F (first i) p • Run.cell K p 0; { toFun:=f,map_add':=fun x y=>by unfold f; simp_rw [show ∀ p q:Site c, Run.cell (x+y) p q=Run.cell x p q+Run.cell y p q from fun i j=>rfl,smul_add,Finset.sum_add_distrib],map_smul':=fun z x=>by unfold f; simp_rw [Run.cell_scale,Finset.smul_sum]; exact sum_congr rfl fun i _=>smul_comm .. }
lemma coats(x:Cover)(w:Walk):Massive.Cylinder.ap c (stop x w)= Massive.Cylinder.ap c x*shimmer 0 (wrap c x) w:=by
      induction w generalizing x with| nil=> simp[shimmer,stop]|cons i l ih=> rw [stop, shimmer, ih, map_add,wrap_vec, Massive.Patria.shimmers,mul_assoc]; -- order
lemma slot : R (X.dept 0 1)= let p:=stop (0:Site c) X.w; (Nw F (first 0) p*shimmer 0 (0:Site c) X.w) • wave X.B :=by
    let p:=stop (0:Site c) X.w
    have he(a:Site c):Run.cell (X.dept 0 1) 0 a=if p=a then shimmer 0 (0:Site c) X.w • wave X.B else 0:=by
        unfold Gleam.dept onSpin; rw [Eyrie.pinned, ride_mul,board, Equiv.trans_refl]; rw [show Equiv.addRight _ 0=p from (wrap_stop ..).symm, Sparks.rack, Matrix.smul_mul,one_mul]
    change (∑ v:Site c,_)=_; rw [sum_eq_single p]; rw [he,if_pos rfl,smul_smul]
    · intro j _ h; rw[he,if_neg h.symm,smul_zero]
    simp
noncomputable def lyra : Spike →L[ℂ] Bundle := LinearMap.toContinuousLinearMap { toFun:=Lat.wave,map_add':=fun x y=> (Lat.wave_add x y).symm,map_smul':=fun s x=> Massive.Oriole.waveP x s}
lemma grants (h:8*X.w.length<c.val): R (X.dept (0:Site c) 1)=lyra (pen X) :=by
     rw [slot]; let P:=stop (0:Cover) X.w; let p:=stop (0:Site c) X.w; have ht:p=wrap c P:= Eq.trans (wrap_stop ..) (zero_add _)
     have hb(i:Axis):Int.natAbs (P i) ≤ X.w.length:= (grand ..).trans (stopBud _); have hv:Lattice.lift p=P:=lift_eq_iff.mpr ⟨ht,fun i=>by have hx:=hb i; omega⟩; let χ:=F.χ ((c.val:ℝ)⁻¹ • Massive.vector P)
     have hχ: χ=1:=by
          apply F.near; intro i; change |((c.val:ℝ)⁻¹) * (P i:ℝ)|≤_; rw[abs_mul,abs_of_nonneg (by positivity),mul_comm,←div_eq_mul_inv,div_le_iff₀ (by positivity)]
          rw [← Int.cast_abs,← Int.natCast_natAbs,Int.cast_natCast]; have hx:8*(Int.natAbs (P i):ℝ)≤ c.val:=by exact_mod_cast (Nat.le_trans (Nat.mul_le_mul_left 8 (hb i)) h.le);
          linarith
     have hz:Massive.Cylinder.ap c P=shimmer 0 (0:Site c) X.w:=by
          rw [show P= _ from rfl]; simpa [Massive.Cylinder.ap] using coats (c:=c) (0:Cover) X.w -- unfold?
     have he : shimmer 0 (0:Site c) X.w*shimmer 0 (0:Site c) X.w=1:=by obtain h|h:= Stew.glisten (0:Site c) (0:Site c) X.w<;>simp[h]
     change (_*_) • _= _; rw[N_one,Np,hv, show F.χ _ = 1 from hχ,Complex.ofReal_one,one_mul,hz,mul_right_comm, he,one_mul,pen,map_smul]; rfl
lemma hopes : ‖R (X.dept (0:Site c) 1)‖ ≤ (X.w.length:ℝ)*(‖lyra‖*‖X.B‖):=by
     rw [slot]; let p:=stop (0:Site c) X.w; change ‖(_*_) • _‖≤ _; rw [norm_smul,norm_mul]; have h:‖shimmer 0 (0:Site c) X.w‖=1:=by obtain h|h := Stew.glisten (0:Site c) (0:Site c) X.w <;> simp [h]
     rw [h,mul_one]; apply mul_le_mul _ (lyra.le_opNorm _) (norm_nonneg _) (by positivity); have hp:= Eyrie.stopped X.w (0:Site c); have ht:pdist p≤ X.w.length:=by simpa [← separation_comm p,separation] using hp -- inspect
     exact (N_price F p 0).trans (Nat.cast_le.mpr ht)
lemma wing(h:0<η): c.val * ‖R (X.dept 0 1)-lyra (pen X)‖ ≤ 16*‖lyra‖*Reserves.polyPrice η 2* X.rate η :=by
     by_cases hv :8*X.w.length<c.val; · rw [grants F X hv,sub_self,norm_zero,mul_zero]; unfold Gleam.rate Reserves.polyPrice; positivity
     push_neg at hv; let b:ℝ:=X.w.length; let U:=‖lyra‖; let Z:=‖X.B‖; have he:0 ≤ b:=by unfold b; positivity
     have ht:‖lyra (pen X)‖ ≤ U*(b*Z):=(lyra.le_opNorm _).trans (mul_le_mul_of_nonneg_left (peg_cash _) (norm_nonneg _))
     apply le_trans (b:= (8*b)*(b*(U*Z)+U*(b*Z))) ((mul_le_mul (show (c.val:ℝ)≤ 8*b from by unfold b; exact_mod_cast hv) ((norm_sub_le ..).trans (add_le_add (hopes ..) ht)) (norm_nonneg _) (by positivity)))
     have hh : b^2 ≤ Reserves.polyPrice η 2 * Real.exp (η*b):=(pow_le_pow_left₀ he (le_add_of_nonneg_left zero_le_one) 2).trans (polynomial_cost h (by positivity) 2); unfold Gleam.rate; change _≤ _* (_ *_); refine le_trans (b:=16*U*(b^2)*Z) (le_of_eq (by ring)) ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by unfold U; positivity : 0 ≤16 * U)) (norm_nonneg X.B)).trans_eq (by unfold b U; ring))
-- uniform
variable {W:Plan j}{V:Train j}
lemma structural {I:Type}{G:I→Gleam}(h:0<η)(H:Rudder.Wages (4*η) a G)(hp:Rudder.Shows G (fun n t=> Pine.wood W t V)): c.val * ‖R (Pine.wood W 0 V 1)-wave (Lat.gamma 0)‖ ≤ 16*‖lyra‖* Reserves.polyPrice (4*η) 2 * a:=by
     let L:=(R).toContinuousLinearMap; have hhh:= (L.hasSum (hp c 0 1)).sub (lyra.hasSum (venture h H hp)); let f:=fun i=> L ((G i).dept (0:Site c) 1)-lyra (pen (G i)); rw[← show (∑' i,f i)=Rod c F 0 (Pine.wood W 0 V 1)-wave (Lat.gamma 0) from hhh.tsum_eq]; have ht:Summable fun i=>‖f i‖:=Summable.norm hhh.summable; apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm ht) (Nat.cast_nonneg _)).trans; rw [← tsum_mul_left]; let p:ℝ:=16*‖lyra‖* Reserves.polyPrice (4*η) 2
     apply ((ht.mul_left (c.val:ℝ)).tsum_le_tsum (fun i=> wing F _ (by positivity)) (H.val.mul_left p)).trans; rw[tsum_mul_left]; exact mul_le_mul_of_nonneg_left H.cap (by unfold Reserves.polyPrice; positivity)
-- invoice true for ALL Ann.Largo.Qu.
lemma rooftop (W:Plan j)(H:Taper):∃ C:ℝ,0<C ∧ ∀ (c:Side)(V:Train j), ‖Rod c H 0 (Pine.wood W 0 V 1)-wave (Lat.gamma 0)‖ ≤ C/(c.val:ℝ):=by
     obtain ⟨t,P,hp,hV,h⟩:= pays_all W; let C:=1+16*‖lyra‖* Reserves.polyPrice t 2*P; refine ⟨C,?_,fun c V=>?_⟩; · unfold C Reserves.polyPrice; positivity
     obtain ⟨I,G,h1,h2⟩:= h V
     let η':=t/4; have ht:4*η'=t:=by unfold η'; ring
     have h:=structural (c:=c) H (show 0<η' from div_pos hp (by norm_num)) (ht.symm ▸ (show Rudder.Wages t P G from h1) : Rudder.Wages (4*η') P G) h2; rw [ht,mul_comm (c.val:ℝ)] at h; exact (le_div_iff₀ (by positivity : 0 < (c.val:ℝ))).mpr (h.trans (le_add_of_nonneg_left zero_le_one))
end YM.QCD.Entr.Goals
#print axioms YM.QCD.Entr.Goals.rooftop
