import YM.QCD.Rain.Air
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rain
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {c L:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar Acre Rails Pressure ConnectedActivityE6 Cost Free Pine
open Jets.Touch Leaf LeafM Tee Eyrie
-- footprint of roots
lemma basics (L: Side) (l:ℕ): Seat L 0 (fun i=> ((sFirst L l (run L i)).val:ℝ)):=by
    let r i:= radiusB (run L i); have hp:Seat L 0 (fun x=> (r x:ℝ)):=by
          apply Seat.compares (Seat.timesL Seat.radius 4); filter_upwards [meters L] with x hx
          rw [abs_of_nonneg (by positivity)]; apply le_trans _ (le_abs_self _); unfold r; exact_mod_cast hx -- defeq rad
    have hh:= (((hp.comb (Seat.numbers 1)).powered 2)); rw [zero_mul] at hh
    have he:=(((hp.timesL (12*(l:ℝ))).comb (Seat.numbers 1)).comb (hh.timesL 128)).timesL ((486:ℝ)*L.val)
    refine he.compares (Eventually.of_forall fun i=>?_)
    let b:= r i; let c:=sFirst L l (run L i); rw [abs_of_nonneg (by positivity)]; apply le_trans _ (le_abs_self _); change (c.val:ℝ) ≤ 486*(L.val:ℝ)*(12*l*b+1+128*(b+1:ℝ)^2)
    have hv (x:ℕ): L.val^(Nat.log L.val x+1) ≤ (x+1)*L.val:=by
          rw [pow_succ]; rcases x.eq_zero_or_pos with hz|hz
          · rw [hz,Nat.log_zero_right]; simp
          exact Nat.mul_le_mul_right _ ((Nat.pow_log_le_self _ (by omega : x ≠0)).trans (by omega))
    let X:= 12*l*b; let Y:= 128*(1+b)^2
    have hY: L.val^visual L l (run L i) ≤ (X+1+Y)*L.val:=by
          let A:= visual L l (run L i); have hz: A=max (Nat.log L.val X+1) (Nat.log L.val Y+1):=by unfold A visual X Y rootX; rw [← mul_assoc] -- test
          change _^A ≤ _
          rw [hz]; cases le_total (Nat.log L.val X+1) (Nat.log L.val Y+1) with
          | inl z=> rw [max_eq_right z]; exact (hv Y).trans (Nat.mul_le_mul_right _ (by omega))
          | inr z=> rw [max_eq_left z]; exact (hv X).trans (Nat.mul_le_mul_right _ (by omega))
    have he :c.val= 486*(L.val^visual L l (run L i)):=by unfold c sFirst boostF stellar; simp; ring
    apply le_trans ((Nat.cast_le (α:=ℝ)).mpr (show c.val ≤ 486*((X+1+Y)*L.val) by rw [he]; omega))
    unfold X Y; push_cast; ring_nf; exact le_rfl
lemma bad_norm {D:Sheet c}(hv:‖D‖ ≤ d): Cost.Floor (-d) D:=by
     intro x; unfold Cost.form; have he:= (op D).le_opNorm x; rw [← Matrix.cstar_norm_def] at he
     have hp:(inner ℂ x (op D x)).re ≥ -(‖x‖*(d*‖x‖)):=by
           have hg:= Complex.abs_re_le_norm (inner ℂ x (op D x)); exact ((abs_le.mp (hg.trans ((norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))) (norm_nonneg _))))).1)
     linarith only [hp]
-- actual Wilson extension.P
lemma shapely (G:Plan j)(v:YM.Next.Free.Train j)(V:Grid c)(h:‖TouchL‖ * ‖settled V-settled 1‖ ≤ (c.val:ℝ)⁻¹): Cost.Floor (G.μ/(c.val:ℝ)^2) (wood G 0 v V):=by
   intro X
   apply le_trans _ (engrave G _ v V X); rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<(c.val:ℝ)^2)]; have hp:=pow_le_pow_left₀ (norm_nonneg _) (ballot V X h) 2
   linarith only [mul_le_mul_of_nonneg_left hp G.price.le]
lemma glows (X:Sheet c)(U:Matrix (Modes c N) (Modes c N) ℂ)(hp:U=copies N X) (h: Cost.Floor a X) : Cost.Floor a U:=by
    intro x; rw [hp]; let y i:Vec (Row c):= WithLp.toLp 2 fun k=> x (k,i); have he : ‖x‖^2 = ∑ i, ‖y i‖^2 :=by rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, sum_comm]; simp_rw [EuclideanSpace.norm_sq_eq]; rfl
    rw [he,mul_sum]; apply (sum_le_sum fun i _=> h (y i)).trans_eq
    simp_rw [Cost.form,← Complex.re_sum]; apply congr_arg; rw [PiLp.inner_apply,Fintype.sum_prod_type (α₁:=Row c),sum_comm]; refine sum_congr rfl fun i _=> ?_; rw [PiLp.inner_apply]; refine sum_congr rfl fun k _=>?_ ; apply (congr_arg (inner ℂ (y i k))); change ∑ j: Row c, X k j * x (j,i)= ∑ j:Modes c N, copies N X (k,i) j * x j; rw [Fintype.sum_prod_type (α₁:=Row c)]; simp only [copies, Matrix.blockDiagonal_apply,ite_mul,zero_mul,sum_ite_eq,mem_univ, if_true]
set_option maxHeartbeats 750000 in
lemma foliage (G:Plan j)(ha:0<a)(hd:0<d)(A C:ℝ)(L:Side)(N l:ℕ)(η:ℝ)(ht:0<η):∀ᶠ x in atTop,let c:=sFirst L l (run L x);∀ (X:Garden.Offer 1 a A)(Y:Garden.Offer 2 d C)(o:YM.Next.Free.Train j)(V: Grid c)(t:ℝ), |t|≤ haloK L x→ ‖TouchL‖ *‖settled V-settled 1‖ ≤ (c.val:ℝ)⁻¹→ let M:=wood G 0 o V+trunkM X Y (haloK L x) t c V; let W:= Lat.copies N M; let r:= (G.μ/(c.val:ℝ)^2)/2; 0<W.det.re∧ (W.det.re:ℂ)=W.det∧ ‖W⁻¹‖ ≤ fan L η x^2 ∧ r^Fintype.card (Modes c N) ≤W.det.re:=by
    obtain ⟨δ,T,n,hx,hT,H⟩:=vaultP ha hd (show (0:ℝ) ≤0 from le_rfl) C A
    let f x:= sFirst L l (run L x); let g x:ℝ:= (f x).val
    have hh:= basics L l; have he:= ((Rate.power (G:=su) (L:=L) (a:=-(1/32:ℝ))).mul_left (T*2)); have hv: Rate su L _ (fun x=>T*2*haloK L x*(g x^2)):= he.mul ((hh.ruled).pow 2)
    filter_upwards [eventually_ge_atTop (0:ℝ),kentucky (A:=1) L (by norm_num), hv.below (by norm_num) (G.μ/2) (half_pos G.price), (((hh.powered 2).timesL (2*G.μ⁻¹)).ponies (chip_r L η)).shrinks (by push_cast; nlinarith) zero_lt_one] with x hz hX he ht' c X Y o V d h hY M W r
    have hu:0<r:=by unfold r; have hp:= G.price; positivity
    have hg:0<haloK L x:=hX.1; have hu':haloK L x≤1:=hX.2.1
    have hT' :0≤T*(haloK L x+|d|):=mul_nonneg hT.le (add_nonneg hg.le (abs_nonneg _)); have hΩ:=H X Y c n le_rfl (haloK L x) d hg hu'
    have hv': ‖trunkM X Y (haloK L x) d c V‖ ≤ T*(haloK L x+|d|):=hΩ.value (mul_pos hx (sq_pos_of_pos hg)) le_rfl hT' V
    have hL:= shapely G o V hY
    have hK : T*(haloK L x+|d|) ≤r:=by unfold r; rw [div_right_comm]; apply (le_div_iff₀ (by positivity)).2; have ht: ↑c.val=(g x:ℝ):=rfl; rw [ht]; apply le_trans _ ((le_abs_self _).trans he); apply mul_le_mul_of_nonneg_right (by linarith only [mul_le_mul_of_nonneg_left h hT.le]) (by positivity)
    have hh:X=X:=rfl
    have ht: Cost.Floor r M:=(hL.add (bad_norm hv')).lower (by unfold r at hK ⊢; linarith only [hK]); have hm : Chiral (chirality c) M:= unity (spinO ..) (tiedStar X Y V ha hd hg hu')
    have hp:0 <M.det.re:= det_pos chi_sq hm hu ht
    have hW:W.det=(↑(M.det.re ^ N):ℂ):= Eq.trans (copies_det ..) (by rw [Complex.ofReal_pow,(determinant_real chi_sq hm : (M.det.re:ℂ) = _)])
    have hR:0 <W.det.re:=by rw [hW,Complex.ofReal_re]; positivity
    have hs:(W.det.re:ℂ)=W.det:=by rw [hW,Complex.ofReal_re];
    have hd:= glows M W rfl ht; refine ⟨hR,hs,(hd.reciprocal hu).trans ?_,?_⟩
    · have h:=fan_pos L η x -- edit
      unfold r; have hχ₁ : |(2*G.μ⁻¹ * (c.val:ℝ)^2)*(fan L η x ^ 2)⁻¹| ≤ 1:= ht'; apply le_trans _ ((div_le_one (sq_pos_of_pos h)).1 ((le_abs_self _).trans (show |2*G.μ⁻¹ * (c.val:ℝ)^2/(fan L η x ^ 2)| ≤ _ from (by rw [div_eq_mul_inv]; exact hχ₁)))); exact le_of_eq (by simp [div_eq_mul_inv]; ring)
    have he:= min_det _ hu.le hd.price; rwa [← hs,Complex.norm_real,Real.norm_of_nonneg hR.le] at he
end YM.QCD.Rain
