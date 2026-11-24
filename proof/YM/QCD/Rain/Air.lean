import YM.QCD.Rain.Drop
/-!
# Gentle climate near a trivial connection; no N-scale factors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rain
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {c L:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar Acre Rails Pressure ConnectedActivityE6 Cost Free Pine
lemma orbitM (i:Axis) {c:Side}: shift (0:Site c) 1 i ^ c.val= -1:=by
     have ht (p:Site c) : cis (menu p i)^c.val= -1:=by
          let k:=lift p i; let v:=cis (k*(2*Real.pi)); have hp: v=1:=by unfold v cis; push_cast; rw [show _ * Complex.I = (k:ℂ)*(2*Real.pi*Complex.I) from (by ring), Complex.exp_int_mul_two_pi_mul_I]; -- lemma
          unfold cis; rw [← Complex.exp_nat_mul,show (c.val:ℂ)*_= ↑((k:ℝ)*(2*Real.pi) + (-Real.pi))*Complex.I from ?_]; rotate_left
          · change _*((↑((c.val:ℝ)⁻¹*((2*(k:ℝ)-1)*Real.pi)):ℂ)*_)= _; push_cast; have he:(c.val:ℂ)≠0:=by exact_mod_cast c.pos.ne'
            field_simp; ring
          change cis (_+_) = _; unfold v at hp; rw [cis_add,hp,one_mul, cis_trig]; simp
     let Y p:= cis (menu (p:Site c) i); have hh (n:ℕ) : peel (shift (0:Site c) 1 i ^n)= lined fun j=> (Y j)^n • 1:=by
           induction n with
           | zero=> simp only [pow_zero,peel_one,one_smul]; exact ridden.symm
           | succ n ih=> rw [pow_succ,peel_mul,ih, peel_shift,lined_law]; apply congr_arg lined; funext p; simp only [Pi.mul_apply,mul_smul_comm,smul_mul_assoc,one_mul,pow_succ]; unfold Y; rw [smul_smul]; ring_nf
     refine peel_injective ?_; rw [hh]; unfold Y; simp_rw [ht,neg_one_smul, show peel (-(1:Sheet c))= -1 by unfold peel; simp [leaf_u _|>.1]]; unfold lined; have he: (fun _:Site c=>-(1:Bundle))=(-1:Site c→Bundle):=rfl; have hh : rides (Equiv.refl (Site c)) (-(1:Site c→Bundle))=( -(1:ℂ)) • rides (Equiv.refl (Site c)) 1:=by rw [ride_smul]; simp
     rw [he,hh, neg_one_smul,show rides (Equiv.refl (Site c)) 1=(1:Sheet c) from ridden]
lemma ballot (V:Grid c) (U:Vec (Row c)) (h:‖TouchL‖ * ‖settled V-settled 1‖ ≤ (c.val:ℝ)⁻¹): ‖U‖ ≤ (c.val:ℝ) * estate 0 V U:=by
    let y:=shift 0 (1:Grid c) 0; let B:=estate 0 V U; let R:= (shift 0 V 0); let a:ℝ:= c.val
    have hh:‖y-R‖≤ a⁻¹:=by
        rw [norm_sub_rev]; apply le_trans _ h; have he:= march_budget 0 (posDir 0) (settled V) (settled 1); simp_rw [marching] at he; exact he
    have hm: ‖op y U-U‖ ≤ a⁻¹ * ‖U‖+B:=by
         have he : op y U-U= op (y-R) U+(op R U-U):=by simp
         rw [he]; apply (norm_add_le ..).trans; refine add_le_add ?_ ((leg_travels 0 V U (posDir 0)).le.trans (dividends ..))
         exact ((op (y-R)).le_opNorm U).trans (mul_le_mul_of_nonneg_right (by rw [← Matrix.cstar_norm_def]; exact hh) (norm_nonneg _))
    let g:=a⁻¹ * ‖U‖+B; have hP(n:ℕ): ‖op (y^n) U-U‖ ≤ n*g:=by
       induction n with
       | zero=> simp
       | succ n ih=>
            rw [pow_succ',map_mul,ContinuousLinearMap.mul_apply]; rw [show op y (op (y^n) U)-U = op y (op (y^n) U-U)+(op y U-U) from ?_] -- next. stmt risk
            · apply (norm_add_le ..).trans; rw [unitary_moves _ (shift_u ..), Nat.cast_succ,add_mul,one_mul]; exact add_le_add ih hm
            rw [map_sub]; abel
    have hz:= hP c.val; rw [show y^c.val = -1 from orbitM _] at hz; simp only [map_neg,ContinuousLinearMap.neg_apply,map_one,ContinuousLinearMap.one_apply] at hz; rw [show -U-U= -(2:ℂ) • U from (by rw [neg_smul,two_smul]; abel),norm_smul,norm_neg] at hz; have he:0<a:=Bloch.side_pos c
    change _ ≤ a*B; change _ ≤ a*g at hz; unfold g at hz; rw [mul_add,← mul_assoc, mul_inv_cancel₀ he.ne',one_mul] at hz; norm_num at hz; linarith
end YM.QCD.Rain
