import YM.Clink.Pale
/-! Arc for combined series in same offsets. Post payment uniform within plate. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QCD.Entr.Meridian
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ C ξ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
open WardBin.Lies Eyrie Rudder Paths
variable (W:Bloom k)(i j: Walk)(o:Site c)(X:Grid c)
local notation "sY"=> stop o i
local notation "N'"=> nursery W i j o
local notation "v"=> stop (stop o i) j
local notation "LW"=> (twig W)
local notation "Q"=> episode W i j o
lemma tillQ (f:Fin k) :let x:=(W.petals f).offset; (wrap _ x + (sY))∈ N':=by
       intro x; refine mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨x,mem_insert_of_mem (mem_biUnion.mpr ⟨f,mem_univ _,?_⟩),rfl⟩)); let A:=W.petals f; exact mem_union_right _ (by change x∈ List.toFinset (Lattice.visits x _); simp [Lattice.visits,square])
lemma guardF (h:Healthy p.threshold N' X)(f:Fin k) : ‖(W.petals f).atSite X (sY)‖≤ p.threshold:=by
       let P:=W.petals f; let z:= wrap c P.offset + (sY); change ‖P.atSite X _‖ ≤ _; rw [recognized]; apply (su.curvature_norm _).trans; rw [torch_pay]; by_contra hh; let V: Face (Per c):=(z,P.plaq); apply Finset.disjoint_left.mp h (show z∈N' from tillQ ..); refine ((flags_spec ..).2 ⟨V,?_,lt_of_not_ge hh⟩); unfold RG.touched; simp [V,Lattice.visits,Lattice.square]
-- zero excluded Berry; hp cost core from Θ. mask V even. real track
open scoped InnerProductSpace
lemma shadesR (h:Healthy p.threshold N' X)(ξ:ℝ)(hξ:0<ξ)(hk:0<k) : ‖episode W i j o ξ (settled X)‖ ≤ W.price*p.threshold:=by
       let A:= satin W (sY) ξ X; have ht:‖A‖ ≤ p.threshold^k*W.price:=by
              apply le_trans (b:=‖W.taste X (sY)‖); · unfold A; rw[vet,norm_smul]; rw[Complex.norm_real,norm_prod]; apply mul_le_of_le_one_left (norm_nonneg _); apply prod_le_one; intro t ht; exact norm_nonneg _; intro t ht; rw [Real.norm_of_nonneg (rate_dog W X hξ (sY) t).1]; exact (rate_dog W X hξ (sY) t).2
              unfold Bloom.taste Bloom.hues Bloom.price; rw [mul_sum]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro t _; rw [norm_smul,Complex.norm_real,norm_prod]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _);
              simpa only [prod_const,card_univ,Fintype.card_fin] using Finset.prod_le_prod (s:=univ) (g:=fun (_:Fin k)=>p.threshold) (f:=fun i': Fin k=> ‖((W.petals i').atSite X (sY)) (t i')‖) (fun _ _=> norm_nonneg _) (fun l _=> by rw [Real.norm_eq_abs,← EuclideanSpace.basisFun_inner]; apply (abs_real_inner_le_norm ..).trans; rw[OrthonormalBasis.norm_eq_one,one_mul]; exact guardF W i j o X h l)
       unfold episode; rw [Pi.mul_apply,Pi.mul_apply,satin_eq]; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_right (norm_nonneg _) (coiled ..)).trans; apply (norm_mul_le ..).trans; apply (mul_le_of_le_one_left (norm_nonneg _) (coiled ..)).trans; rw[mul_comm]; apply ht.trans; exact mul_le_mul_of_nonneg_right ((pow_le_pow_of_le_one p.threshold_pos.le p.threshold_le hk).trans_eq (pow_one _)) W.price_nn
lemma van (ξ:ℝ)(hξ:0<ξ)(hk:0<k): episode W i j o ξ (settled 1)=0:=by
       unfold episode; rw [Pi.mul_apply,Pi.mul_apply,satin_eq,show satin W (sY) ξ 1=0 from ?_,mul_zero,zero_mul]
       rw [vet]; suffices h: W.taste (1:Grid c) (sY)=0 by rw[h,smul_zero]
       unfold Bloom.taste Bloom.hues; simp_rw [Bloom.slot_tail]; let x: Fin k:= ⟨0,hk⟩; refine sum_eq_zero fun i _=>?_ ; rw [Finset.prod_eq_zero (i:=x) (mem_univ _) ?_,Complex.ofReal_zero,zero_smul]; rfl
-- factor harvest geometry exponent by true Pay (not Ticket)
local notation "L"=>harvestK W i j
lemma rentC (ha:σ/2=t)(ht:0<t)(hp:0 ≤ P)(h:0<ξ)(hξ:ξ≤1)(hk:0<k)(hh:i.length+j.length≤ 1+W.tail.length) (hb:0<B)(he:0 ≤ η)(hu:η/B ≤ t) : let T:=rent η B N'; let A:= Real.exp (η*(3+2*(k:ℝ))+2*t)*‖TouchL‖^2*P^k
      T*(harvestK W i j t P ξ) ≤ A* W.paid σ*ξ :=by
       intro T A; let d:= (twig W).length; let u:ℝ:= (d:ℝ)+i.length+j.length; have hhR:T ≤Real.exp (η*(3+2*(k:ℝ))+t*u):=expense W i j o hb he hu
       rw [show L t P ξ=Real.exp (t*u)*‖TouchL‖^2*P^k*ξ^k*W.price from ?_]; swap
       · unfold harvestK cal u d; rw [mul_add,mul_add,Real.exp_add, Real.exp_add, mul_pow]; ring
       let z:=Real.exp (η*(3+2*(k:ℝ))+t*u); apply (mul_le_mul_of_nonneg_right hhR (by positivity [W.price_nn])).trans; have hf:u≤ 1+W.span:=by
           have hv:(i.length:ℝ)+j.length ≤1+(W.tail.length:ℝ):= by exact_mod_cast hh -- shadow hh
           unfold u d Bloom.span Atom.length twig; push_cast; push_cast at hv; linarith
       have hx:0≤ σ:=by linarith
       have hp': ξ^k≤ξ:= (pow_le_pow_of_le_one h.le hξ hk).trans_eq (pow_one _); have hM: Real.exp (η*(3+2*(k:ℝ))+t*u) * Real.exp (t*u) ≤ Real.exp (η*(3+2*(k:ℝ))+2*t)*Real.exp (σ*W.span):=by
            simp_rw [← Real.exp_add]; apply Real.exp_monotone; rw [show σ=t*2 from (by linarith)]; nlinarith
       unfold A Bloom.paid; calc
           _=(Real.exp (η*(3+2*(k:ℝ))+t*u)*Real.exp (t*u))*(‖TouchL‖^2*P^k*W.price)*ξ^k:=by ring
           _≤ (Real.exp (η*(3+2*(k:ℝ))+2*t)*Real.exp (σ*W.span))*(‖TouchL‖^2*P^k*W.price)*ξ:=mul_le_mul (mul_le_mul_of_nonneg_right hM (by positivity [W.price_nn])) hp' (by positivity) (by positivity[W.price_nn])
           _= _:=by ring
end YM.QCD.Entr.Meridian
#print axioms YM.QCD.Entr.Meridian.van
#print axioms YM.QCD.Entr.Meridian.shadesR
#print axioms YM.QCD.Entr.Meridian.rentC
